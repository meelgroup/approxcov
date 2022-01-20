## /***********[approxmaxcov_mv.py]
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
import shutil
import random
import subprocess
import sys
from pathlib import Path

#functions to parse CASA modelfile and constraints into smtlib format. Inputfile is a .constraints file, _2way.model file is expected nearby.
def convert_cl(clause):
  if len(clause) == 1:
      return str(clause[0])
  else:
      return '(or ' + str(clause[0]) + ' ' + convert_cl(clause[1:]) +')'

def parse_CASA_bv(inputfile, outputfile):    
    modelfile = inputfile[:-12]+ '_2way.model'
    with open(modelfile) as f:
        lines = f.readlines()
        varsizes = list(map(lambda x : int(x.strip()), lines[2].strip().split(' ')))
    aggsizes = list(itertools.accumulate(varsizes))
    total = sum(varsizes)
    valuetovar = {}
    j=0
    for i in range(total):
        valuetovar[i] = j
        if aggsizes[j] == i+1 :
            j +=1
    maxVal = max(varsizes)
    maxValBits = math.ceil(math.log2(maxVal+1))
    clauses = []
    with open(inputfile) as f:
        lines = f.readlines()
        lines = lines[2::2]
        for line in lines:
            l = line.strip().split(' ')
            modif = l[0] == '+'
            clause = []
            for i in range(1,len(l)):
                if l[i] == '-':
                    modif = False
                elif l[i] == '+':
                    modif = True
                else:
                    number = int(l[i])
                    v = valuetovar[number]
                    val = number - aggsizes[v-1] if v > 0 else number
                    el = '(= v_' + str(v) + ' (_ bv' + str(val) + ' '+ str(maxValBits) + '))' 
                    if not modif:
                        el = '(not ' + el + ')'
                    clause.append(el)
            clauses.append(clause)
    with open(outputfile, 'w+') as fo:
        fo.write(';; ' + ' '.join(map(str, varsizes)) + '\n')
        fo.write('(set-logic QF_BV)\n')
        for i in range(len(varsizes)):
            fo.write('(declare-fun v_' + str(i) +' () (_ BitVec '+ str(maxValBits) +'))\n')
            fo.write('(assert (and (bvuge v_' + str(i)+ ' (_ bv0 '+ str(maxValBits) +')) (bvult v_' + str(i)+ ' (_ bv' + str(varsizes[i]) + ' ' + str(maxValBits) +'))))\n')
        for cl in clauses:
            fo.write('(assert '+ convert_cl(cl) +')\n')
      
###########################################################################################      
      
def get_combinations_nb(z3file, size, outputfile, combs):
    tmpCNF = z3file[:-4] + '.tmp'
    with open(z3file) as f:
      varsizes = list(map(lambda x : int(x.strip()), f.readline()[3:].strip().split(' ')))
    feasibleCombs = []
    allComb = []
    start = time.time()
    if size == 1:
        allComb = [[(x,y)] for x in range(0, len(varsizes)) for y in range(varsizes[x])]
    else:
        for precomb in combs[-1]:  # expected to be sorted, add only literals with greater value
            first = precomb[-1][0] +1
            for l in range(first, len(varsizes)):
                for v in range(varsizes[l]):
                    newComb = precomb[:] + [(l,v)]
                    allComb.append(newComb)
    f = open(outputfile, "w")
    total = len(allComb)
    print("Total combinations to check " + str(total))
    curPerc = 0.0
    maxVal = max(varsizes)
    maxValBits = math.ceil(math.log2(maxVal+1))
    for i in range(len(allComb)):
        comb = allComb[i]
        shutil.copyfile(z3file, tmpCNF)
        with open(tmpCNF, 'a+') as ftmpCNF:
            for lit in comb:
                ftmpCNF.write('(assert  (= v_' + str(lit[0]) + ' (_ bv' + str(lit[1]) + ' ' + str(maxValBits) +')))\n')
            ftmpCNF.write('(check-sat)\n')    
        cmd = 'z3 ' + tmpCNF + ' > z3res.txt' 
        os.system(cmd)
        with open('z3res.txt') as fres:
            lines = fres.readlines()
            s = 'UNSAT'
            if len(lines) > 0 and lines[0].strip() == 'sat':
              s= 'SAT'
        if s != 'UNSAT':
            f.write(','.join(map(str, comb)) + '\n')
            feasibleCombs.append(comb)
        if i / total > curPerc + 0.05:
            curPerc += 0.05
            print(str(round(100 * curPerc)) + "% done")
    f.close()
    print("Time to get satisfiable combinations " + str(time.time() - start))
    return feasibleCombs             

def generateGFFile(z3file, nVars, varsizes, twise, tmpCNF):
    with open(z3file) as fo:
      lines = fo.readlines()
    maxVal = max(varsizes)
    maxValBits = math.ceil(math.log2(maxVal+1))
    nVarBits = math.ceil(math.log2(nVars+1))
    shutil.copyfile(z3file, tmpCNF)
    with open(tmpCNF, 'a+') as f:
        f.write('\n')
        for i in range(twise):
            f.write('(declare-fun v_' + str(i+nVars) +' () (_ BitVec '+ str(nVarBits) +'))\n')
            
            f.write('(assert (bvult v_' + str(i+nVars)+ ' (_ bv' + str(nVars) + ' ' + str(nVarBits) +')))\n')
        
        for i in range(twise):
            for j in range(i+1, twise):
                f.write('(assert ( not (=  v_'+ str(i+nVars) + ' v_' + str(j+nVars) +  ')))\n')
        
        for i in range(twise):
            f.write('(declare-fun v_' + str(i+nVars+ twise) +' () (_ BitVec '+ str(maxValBits) +'))\n')
            
        for i in range(twise):
            for j in range(nVars):
                f.write('(assert (or (not (= v_'+ str(i+nVars) + ' (_ bv' + str(j) + ' '+ str(nVarBits) +'))) (= v_' + str(i+nVars + twise) + ' v_' + str(j) + ')))\n')
                
        varsmap = {}
        counter =1
        for i in range(nVarBits):
            mask = '(_ bv' + str(int(math.pow(2,i))) +' '+ str(nVarBits) +')'
            for t in range(twise):
                f.write('(declare-fun v_' + str(t+nVars)+'_'+str(i) +' () Bool)\n')
                varsmap['v_'+str(t+nVars)+'_'+str(i)] = counter
                counter +=1
                f.write('(assert (= v_' + str(t+nVars)+'_'+str(i) +' (= (bvand v_' + str(t+nVars)+' '+mask+'  ) '+mask+')))\n')
        for i in range(maxValBits):
            mask = '(_ bv' + str(int(math.pow(2,i))) +' '+ str(maxValBits) +')'
            for t in range(twise):
                f.write('(declare-fun v_' + str(t+nVars+ twise)+'_'+str(i) +' () Bool)\n')
                varsmap['v_'+str(t+nVars+ twise)+'_'+str(i)] = counter
                counter +=1
                f.write('(assert (= v_' + str(t+nVars+ twise)+'_'+str(i) +' (= (bvand v_' + str(t+nVars+ twise)+' '+mask+'  ) '+mask+')))\n')

        keyset = list(varsmap.keys())
        for key in keyset:
            varsmap['-'+key] = -varsmap[key]
        
        f.write("(apply (then simplify (then bit-blast tseitin-cnf)))\n")
    
    try:
        os.remove(tmpCNF + '.out')
    except OSError:
        pass    
    cmd =  'z3 ' + tmpCNF + '> ' + tmpCNF + '.out'  
    os.system(cmd)

    with open(tmpCNF + '.out') as fo:
        lines = fo.readlines()
        lines = lines[2:-2]
    with open(tmpCNF[:-4]+'.cnf', 'w+') as fi:    
        fi.write('c ind ' + ' '.join(map(str, range(1, counter))) + ' 0\n')
        i =0
        maxvar = 0
        cnffilelines = []
        nLines = len(lines)
        while i < nLines:
            line = lines[i].strip()
            lbracket = line.count('(')
            rbracket = line.count(')')
            while lbracket !=rbracket :
                line = line + lines[i+1]
                lbracket = line.count('(')
                rbracket = line.count(')')
                i+=1
            line = line.replace('(or', '')
            line = line.replace(',', '')
            line = line.replace(')', '')
            line = line.replace('(not ', '-')
            line = line.replace('k!', '')
            els = list(filter(None, line.split(' ')))
            els_parsed = list(map(lambda x: varsmap[x] if x in varsmap else(-counter if x=='-0' else (int(x)  + counter if (int(x) >= 0) else int(x) - counter)), els))
            elss = [str(x) for x in els_parsed]
            cnffilelines.append(' '.join(elss)+' 0\n')
            maxline = max(els_parsed)
            maxvar = maxline if maxline > maxvar else maxvar
            i+=1
        fi.write('p cnf ' + str(maxvar) + ' ' + str(len(cnffilelines)) + '\n')
        for line in cnffilelines:
            fi.write(line)
 
def approxComb_nb(z3file, twise, epsilon, delta, seed):
    tmpFile = 'tmp.smt'
    with open(z3file) as f:
      varsizes = list(map(lambda x : int(x.strip()), f.readline()[3:].strip().split(' ')))
    nVars = len(varsizes)
    start = time.time()
    approxOutput='out.pmc'
    divisor = math.factorial(twise)
    generateGFFile(z3file, nVars, varsizes, twise, tmpFile)
    try:
        os.remove(approxOutput)
    except OSError:
        pass
    if seed:
        cmd = 'approxmc --seed ' + str(seed) + ' --epsilon ' + str(epsilon) + ' --delta ' + str(delta) + ' ' + tmpFile[:-4] +  '.cnf' + ' >' + approxOutput  
    else:
        cmd = 'approxmc --seed ' + str(random.randint(1,10000)) + ' --epsilon ' + str(epsilon) + ' --delta ' + str(delta) + ' ' + tmpFile[:-4] +  '.cnf' + ' >' + approxOutput  
    os.system(cmd)    
    with open(approxOutput) as f:
        for line in f:
            if line.startswith('s mc'):
                number= int(line.strip().split(' ')[2].strip())
                result = number // divisor
                break
    print("Approximate number of combinations is " + str(result))
    total_user_time = time.time() - start
    return result

#-----------------------------------------------------------------------------------------------------

def run(Z3, size, outputdir, approx, epsilon, delta, seed):
    if approx:
      start_full = time.time()
      approxComb_nb(Z3, size, epsilon, delta, seed)
      print("Total time: " + str(time.time() - start_full))
    else:
      combs = []
      benchmarkName = os.path.basename(Z3).split('.')[0]
      start_full = time.time()
      for i in range(size):
        print("Generating " + str(i+1) + "-wise combinations")
        combs.append(get_combinations_nb(Z3, i+1, os.path.join(outputdir, benchmarkName + '_' + str(i+1) + '.comb'), combs))
      print("Number of combinations is " + str(len(combs[-1])))
      print("Total time: " + str(time.time() - start_full))
    

if __name__ == "__main__":
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--outputdir", type=str, default="results/", help="output directory", dest='outputdir')
    parser.add_argument("--approximate", action='store_true', help="Computes combinations approximately", dest='approx')
    parser.add_argument("--twise", type=int, help="size of feature combinations. Note that with non-approximate method all combinations with smaller size would be generated", dest='twise')
    parser.add_argument("--delta", type=float, default=0.05, help="Delta for approximate counting", dest='delta')
    parser.add_argument("--epsilon", type=float, default=0.05, help="Epsilon for approximate counting", dest='epsilon')
    parser.add_argument("--seed", type=int, help="Random seed. Unused if approximate is not selected", dest='seed')
    parser.add_argument('Z3', nargs='?', type=str, default="", help='input z3 file with constraints')
    args = parser.parse_args()

    if args.Z3 == '':
        parser.print_usage()
        sys.exit(1)
    if not args.twise:
        parser.print_usage()
        sys.exit(1)

    Path(args.outputdir).mkdir(parents=True, exist_ok=True)
    run(args.Z3, args.twise, args.outputdir, args.approx, args.epsilon, args.delta, args.seed)
