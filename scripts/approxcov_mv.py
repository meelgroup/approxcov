## /***********[approxcov_mv.py]
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

import time
import argparse
import random
import os
import math
import itertools
import sys

# This function can be used to convert sample sets for CASA tool into format used by this script. It assumes that the samples file (*.out) is placed next to the modelfile that is given as an input
def rewrite_output_CASA(modelfile, outfile):
    with open(modelfile) as f:
        lines = f.readlines()
        varsizes = list(map(lambda x : int(x.strip()), lines[2].strip().split(' ')))
    with open(modelfile[:-11] + '.out') as f2:
        lines = f2.readlines()
        samples = []
        for line in lines[1:]:
            samples.append(list(map(lambda x: int(x.strip()), line.strip().split(' '))))
    res = []
    for sample in samples:
        agg =0
        tmp = []
        for i in range(len(sample)):
            tmp.append(sample[i]-agg)
            agg += varsizes[i]
        res.append(tmp)
    fi = open(outfile, 'w+')
    fi.write(' '.join(map(str, varsizes)) + '\n')
    for l in res:                                                                                              
        fi.write('0,' + ' '.join(map(str, l)) + '\n')  
    fi.close()


def getTuples_rec(lst, sizeLeft, trieNode, count, comb):
    if sizeLeft == 1:
        for x in lst:
            if x not in trieNode: 
                trieNode[x] = True
                count[0] +=1
    else:
        for i in range(len(lst) - sizeLeft + 1):
            if lst[i] not in trieNode:
                trieNode[lst[i]] = {}
            trieNodeNew = trieNode[lst[i]]
            combNew = comb[:] + [lst[i]]
            getTuples_rec(lst[i+1 :], sizeLeft -1, trieNodeNew, count, combNew)

def check_coverage_nb(samplefile, size):
    trie = {}
    count = [0]
    with open(samplefile, "r") as f:
        lines = f.readlines()
        for line in lines[1:]:
            s= line.strip().split(',')[1].strip().split(' ')
            s_upd = list(map(lambda x: 'v'+str(x[0])+'.'+x[1], zip(range(len(s)), s)))
            getTuples_rec(s_upd, size, trie, count, [])
    countRes = count[0]
    print("Number of combinations " + str(countRes))
    return countRes

def cnk(n, k):
    if k > n/2:
        k = n-k
    res =1
    for i in range(k):
        res *= n-i
    for i in range(k):
        res //= (i+1)
    return res


def compute_total_n(n, k, varsizes):
    matrix = [[0 for _ in range(k)] for _ in range(n)]
    sum =0
    for i in range(n):
        sum += varsizes[i]
        matrix[i][0] = sum
    mult = 1
    for i in range(k):
        mult *= varsizes[i]
        matrix[i][i] = mult
    for i in range(1,n):
        for j in range(1,k):
            if j<i:
                matrix[i][j] = matrix[i-1][j] + matrix[i-1][j-1]*varsizes[i]
    return matrix

def random_walk(proba):
    return random.random() < proba

def genRandomBoxes_nb(nvars, size, varsizes, number, matrix):
    res = {}
    for ind in range(number):
        box = []
        i = nvars-1
        j = size-1
        while len(box) < size:
            if i == 0:
                box.append(i)
            elif random_walk(matrix[i-1][j]/matrix[i][j]):
                i -=1
            else:
                box.append(i)
                i-=1
                j-=1
        newBox = tuple(sorted(map(lambda x: (x, random.randrange(varsizes[x])), box)))
        res.update({(ind,newBox) : 0})
    return res

def approximate_coverage_nb(samplefile, size, epsilon, delta):
    with open(samplefile, "r") as f:
        lines = f.readlines()
        varsizes = list(map(lambda x : int(x.strip()), lines[0].split(' ')))
        nvars = len(varsizes)     
        matrix = compute_total_n(nvars, size, varsizes)
        total_comb = matrix[nvars-1][size-1]
        nBoxes = math.ceil(3 * math.log(2 / delta) * total_comb / (epsilon*epsilon) / cnk(nvars, size))
        if total_comb <= nBoxes:
            print('There are only ' + str(total_comb) + ' combinations')
            boxes = {}
            for comb in itertools.combinations(range(0,nvars), size):
              combsizes = [list(range(varsizes[x])) for x in comb]
              boxes.update({(0,tuple(sorted(zip(comb,k)))):0 for k in itertools.product(*combsizes)})
        else:
            boxes = genRandomBoxes_nb(nvars, size, varsizes, nBoxes, matrix)
        nBoxes = len(boxes.keys())
        for line in lines[1:]:
            s = list(map(lambda x : int(x.strip()), line.strip().split(',')[1].strip().split(' ')))
            for comb in boxes.keys():
                if boxes[comb] == 0 and all(s[comb[1][i][0]] == comb[1][i][1] for i in range(size)):
                    boxes[comb] = 1
        coveredBoxes = sum(boxes.values())
        countRes = int(total_comb * coveredBoxes  / nBoxes)
        print("Approximate number of combinations " + str(countRes))
    return countRes

def run(samples, twise, isApprox, epsilon, delta):
    start = time.time()
    if isApprox:
        approximate_coverage_nb(samples, twise, epsilon, delta)
    else:
        check_coverage_nb(samples, twise)
    print("Time taken: " + str(time.time() - start))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('samples', type=str, default="", help='Input file with samples')
    parser.add_argument("--twise", type=int, help='The size of combinations', required=True)
    parser.add_argument("--approximate", action='store_true', help="Computes combinations approximately", dest='apprx')
    parser.add_argument("--delta", type=float, default=0.05, help="Delta for approximate counting", dest='delta')
    parser.add_argument("--epsilon", type=float, default=0.05, help="Epsilon for approximate counting", dest='epsilon')
    parser.add_argument("--seed", type=int, help="Random seed. Unused if approximate is not selected", dest='seed')
    
    args = parser.parse_args()
    if args.seed:
        random.seed(args.seed)
    if args.samples == '':
        parser.print_usage()
        sys.exit(1)
    if args.twise <= 0:
        parser.print_usage()
        sys.exit(1)

    run(args.samples, args.twise, args.apprx, args.epsilon, args.delta)
    
