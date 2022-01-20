## /***********[approxmaxcov.py]
# Copyright (c) 2022 Eduard Baranov, Sourav Chakraborty, Axel Legay, Kuldeep S. Meel, Vinodchandran N. Variyam 
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:
# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
# OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
# ***********/


import argparse
import os
import time
import math
import bisect
import pycosat
import sys
import random
from pathlib import Path

def parse_cnf(cnffile):
    clauses = []
    with open(cnffile) as f:
        lines = f.readlines()
        for line in lines:
            if line.startswith("c"):
                continue
            elif line.startswith("p"):
                nVars = int(line.strip().split(' ')[2])
            else:
                literals = list(map(int, line.strip().split(' ')))
                if len(literals) > 1:
                    clauses.append(literals[:-1])
    return nVars, clauses

def combinations(lst, size, acc, res):
    if size == 1:
        for x in lst:
            newComb = acc[:] + [x]
            res.append(newComb)
    else:
        for i in range(len(lst)- size + 1):
            accI = acc[:] + [lst[i]]
            combinations(lst[i+1:], size -1, accI, res)
            
def get_combinations(nVars, clauses, size, outputfile, combs):
    feasibleCombs = []
    allComb = []
    start = time.time()
    if size == 1:
        allComb = [[x] for x in range(-nVars, 0)] + [[x] for x in range(1, nVars+1)]
    else:
        literals = list(map(lambda x : x[0], combs[0]))
        for precomb in combs[-1]:  # expected to be sorted, add only literals with greater value
            first = bisect.bisect_right(literals, precomb[-1])
            for l in range(first, len(literals)):
                if -(literals[l]) not in precomb: 
                    newComb = precomb[:] + [literals[l]]
                    allComb.append(newComb)
    f = open(outputfile, "w")
    total = len(allComb)
    print("Total combinations to check " + str(total))
    #print("Time to generate combinations to check " + str(time.time() - start))
    curPerc = 0.0
    for i in range(len(allComb)):
        comb = allComb[i]
        cnf = clauses[:] + list(map(lambda x : [x], comb))
        s = pycosat.solve(cnf)
        if s != 'UNSAT':
            f.write(','.join(map(str, comb)) + '\n')
            feasibleCombs.append(comb)
        if i / total > curPerc + 0.05:
            curPerc += 0.05
            print(str(round(100 * curPerc)) + "% done")
    f.close()
    print("Time to get satisfiable combinations " + str(time.time() - start))
    return feasibleCombs

#-----------------------------------------------------------------------------------------------------

# Generete clauses corresponding to i < n, where i consists of variables startPos..startPos+bvsize-1
def lessClause(startPos, n, bvsize):
    bitN = [ (n >> i) % 2 for i in range(bvsize)]
    for i, j in enumerate(bitN): #reverse & cutdown end zeroes
        if j:
            bitN = list(reversed(bitN[i:]))
            break
    result = []
    agg = []
    for i in range(len(bitN)):
        if bitN[i]:
            agg.append(-(startPos +i))
        else:
            result.append(agg[:] + [-(startPos +i)])
    result.append(agg)
    return result

# Generete clauses corresponding to i= j => v_i = x_j
def relClause(startPos, n, bvsize, vPos):
    bitN = list(reversed([ ((n-1) >> i) % 2 for i in range(bvsize)]))
    neq = [(startPos + i) * (bitN[i]*2-1) * (-1) for i in range(len(bitN))]
    return [neq[:] + [-n, vPos], neq[:] + [n, -vPos]]

       
# Generete clauses corresponding to i_1 < i_2
def ltClause(startPosFirst, startPosSecond, bvsize):
    if (bvsize==1):
        return [[-startPosFirst],[startPosSecond]]
    else:
        recres = ltClause(startPosFirst+1, startPosSecond+1, bvsize-1)
        return [[-startPosFirst] + cl[:] for cl in recres] + [[startPosSecond] + cl[:] for cl in recres] + [[-startPosFirst, startPosSecond]]
 

    
#vars indexes: [1, nVars] - original, [nVars+1, nVars + fsize*bvsize] - index variables, [nVars + fsize*bvsize + 1, nVars + fsize*bvsize + fsize]
# index i correspond to var=(i+1), indexes starting from 0 rather than from 1
def generateGFCNF(nVars, clauses, fsize, outputFile):
    bvsize = math.ceil(math.log2(nVars+1))
    valueVarsBaseIndex = nVars + fsize*bvsize
    newClauses = []
    for i in range(fsize):
        newClauses.extend(lessClause(nVars + i*bvsize + 1, nVars, bvsize))
    for i in range(fsize-1):
        newClauses.extend(ltClause(nVars + i*bvsize + 1, nVars + (i+1)*bvsize + 1, bvsize))
    for i in range(fsize):
        for j in range(1, nVars+1):
            newClauses.extend(relClause(nVars + i*bvsize + 1, j, bvsize, valueVarsBaseIndex + i + 1))
            
    with open(outputFile, 'w+') as f:
        varList = [i for i in range(nVars + 1, nVars + fsize*bvsize + fsize +1)]
        f.write('c ind ' + ' '.join(list(map(str, varList))) + ' 0\n')
        f.write('p cnf ' + str(nVars + fsize*bvsize + fsize) + ' ' +  str(len(clauses) + len(newClauses)) + '\n')
        for cl in clauses + newClauses:
            f.write(' '.join(list(map(str, cl + [0]))) + '\n')



def approxComb(nVars, clauses, twise, tmpCNF, epsilon, delta, seed):
    approxOutput='out.pmc'
    generateGFCNF(nVars, clauses, twise, tmpCNF)
    
    try:
        os.remove(approxOutput)
    except OSError:
        pass
    if seed:
        cmd = 'approxmc --seed ' + str(seed) + ' --epsilon ' + str(epsilon) + ' --delta ' + str(delta) + ' ' + tmpCNF + ' >' + approxOutput  
    else:
        cmd = 'approxmc --seed ' + str(random.randint(1,10000)) + ' --epsilon ' + str(epsilon) + ' --delta ' + str(delta) + ' ' + tmpCNF + ' >' + approxOutput  
    start = time.time()
    os.system(cmd)
    total_user_time = time.time() - start
    result = -1
    with open(approxOutput) as f:
        for line in f:
            if line.startswith('s mc'):
                number= int(line.strip().split(' ')[2].strip())
                result = number
                break
    print("Approximate number of combinations is " + str(result))
    return result
    


#-----------------------------------------------------------------------------------------------------

def run(dimacscnf, twise, outputdir, apprx, epsilon, delta, seed):
    nVars, clauses = parse_cnf(dimacscnf)
    benchmarkName = os.path.basename(dimacscnf).split('.')[0]
    if apprx:
        start_full = time.time()
        approxComb(nVars, clauses, twise, benchmarkName + '_tmp.cnf', epsilon, delta, seed)
        print("Total time: " + str(time.time() - start_full))
    else:
        combs = []   
        start_full = time.time()
        for i in range(twise):
            print("Generating " + str(i+1) + "-wise combinations")
            combs.append(get_combinations(nVars, clauses, i+1, os.path.join(outputdir, benchmarkName + '_' + str(i+1) + '.comb'), combs))
        print("Number of combinations is " + str(len(combs[-1])))
        print("Total time: " + str(time.time() - start_full))
    

if __name__ == "__main__":
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--outputdir", type=str, default="results/", help="output directory", dest='outputdir')
    parser.add_argument("--approximate", action='store_true', help="Computes combinations approximately", dest='apprx')
    parser.add_argument("--twise", type=int, help="size of feature combinations. Note that with non-approximate method all combinations with smaller size would be generated", dest='size')
    parser.add_argument('DIMACSCNF', nargs='?', type=str, default="", help='input cnf file in dimacs format')
    parser.add_argument("--delta", type=float, default=0.05, help="Delta for approximate counting", dest='delta')
    parser.add_argument("--epsilon", type=float, default=0.05, help="Epsilon for approximate counting", dest='epsilon')
    parser.add_argument("--seed", type=int, help="Random seed. Unused if approximate is not selected", dest='seed')
    args = parser.parse_args()
    
    if args.DIMACSCNF == '':
        parser.print_usage()
        sys.exit(1)

    Path(args.outputdir).mkdir(parents=True, exist_ok=True)
    run(args.DIMACSCNF, args.size, args.outputdir, args.apprx, args.epsilon, args.delta, args.seed)


