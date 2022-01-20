## /***********[approxcov.py]
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
import sys

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

def check_coverage(samplefile, size):
    trie = {}
    count = [0]
    aggrCount = []
    with open(samplefile, "r") as f:
        for line in f:
            s = list(map(int, line.strip().split(',')[1].strip().split(' ')))
            getTuples_rec(s, size, trie, count, [])
            aggrCount.append(count[0])
    countRes = count[0]
    print("Number of combinations " + str(countRes))
    return countRes

def genRandomBoxes(nvars, size, number):
    res = {}
    if cnk(nvars, size) *(2**size) < number:
        print('There are only ' + str(cnk(nvars, size) *(2**size)) + ' combinations')
        import itertools
        coeff = list(itertools.product(range(2), repeat=size))
        for comb in itertools.combinations(range(1,nvars+1), size):
            res.update({(0,tuple(sorted(map(lambda x : x[0] if x[1]==1 else -x[0], zip(comb,k))))):0 for k in coeff})
        return res
    for i in range(number):
        res.update({(i,tuple(sorted(map(lambda x: x if random.randint(0,1) == 1 else -x, random.sample(range(1,nvars+1), size))))):0})
    return res

def cnk(n, k):
    res =1
    for i in range(k):
        res *= n-i
    for i in range(k):
        res /= (i+1)
    return res

def approximate_coverage(samplefile, size, epsilon, delta):
    nBoxes = math.ceil(3 * (2**size) * math.log(2 / delta) / (epsilon*epsilon))
    with open(samplefile, "r") as f:
        nvars = len(f.readline().strip().split(',')[1].strip().split(' '))     
    boxes = genRandomBoxes(nvars, size, nBoxes)
    with open(samplefile, "r") as f:
        for line in f:
            s = list(map(int, line.strip().split(',')[1].strip().split(' ')))
            for comb in boxes.keys():
                if boxes[comb] == 0 and all(s[abs(comb[1][i])-1] == comb[1][i] for i in range(size)):
                    boxes[comb] = 1
    coveredBoxes = sum(boxes.values())
    if len(boxes) < nBoxes:
        countRes = coveredBoxes
    else:
        countRes = int(cnk(nvars, size) * coveredBoxes *(2**size) / nBoxes)
    print("Approximate number of combinations " + str(countRes))
    return countRes

def run(samples, twise, isApprox, epsilon, delta):
    start = time.time()
    if isApprox:
        approximate_coverage(samples, twise, epsilon, delta)
    else:
        check_coverage(samples, twise)
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

    
