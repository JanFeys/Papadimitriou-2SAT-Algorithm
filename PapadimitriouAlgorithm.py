#!/usr/bin/env python3

import time
from math import log
import random
from collections import defaultdict

def evaluate_expr(c1n,b1,c2n,b2):
    #Expressions of the form "b1 OR b2" are evaluated, with c1n and c2n determining if b1 and b2 are negated or not. Hence, if c1n = True and c2n = False, we are evaluating "(NOT b1) OR b2".
    if c1n and c2n:
        return ((not b1) or (not b2))
    elif (not c1n) and c2n:
        return (b1 or (not b2))
    elif c1n and (not c2n):
        return ((not b1) or b2)
    else:
        return (b1 or b2)

def construct_expr_dict():
    #Save a dictionary of the outcomes of the all of the 16 possible clause expressions.
    expr_dict = dict()
    for c1n in [True,False]:
        for c2n in [True,False]:
            for b1 in [True,False]:
                for b2 in [True,False]:
                    expr_dict[(c1n,b1,c2n,b2)] = evaluate_expr(c1n,b1,c2n,b2)
    return expr_dict

def evaluate_cls(cls,rel_cls,vars,expr_dict,unsat_cls,p_changes):
    #Given an expr_dict (used for speeding up the calculation), a list of clauses, a dictionary of relevant clauses for every bit of vars, and a list of vars (bits), we output a set (of clause-ids) which signifies which clauses were NOT satisfied.
    #p_change determines which position changed. If it is "None" then we do a full evaluation. If not, we only evaluate all the clauses that involve p_change.
    if len(p_changes) == 0:
        for cl_idx in range(len(cls)):
            cl = cls[cl_idx]
            if not expr_dict[(cl[0],vars[cl[1]],cl[2],vars[cl[3]])]:
                unsat_cls.add(cl_idx)
    else:
        for p_change in p_changes:
            for cl_idx in rel_cls[p_change]:
                cl = cls[cl_idx]
                if not expr_dict[(cl[0],vars[cl[1]],cl[2],vars[cl[3]])]:
                    unsat_cls.add(cl_idx)
                else:
                    unsat_cls.discard(cl_idx)

def modify_bits(unsat_cls,vars,nr_bits):
    p_changes = []
    unsat_cl_idx = random.sample(unsat_cls, nr_bits) #pick a random unsatisfied clause
    for idx in unsat_cl_idx:
        unsat_cl = cls[idx]
        p_change = random.choice([unsat_cl[1], unsat_cl[3]]) #randomly pick on the two bits
        vars[p_change] = not vars[p_change] #flip the chosen bit
        p_changes.append(p_change)
    return p_changes

def run_Papadimitriou(nr_vars,cls,rel_cls):
    #set number of iterations and calculate a dictionary of all expressions
    nr_it = int(log(nr_vars)/log(2))
    expr_dict = construct_expr_dict()
    
    for i in range(nr_it):
        #select random list of true and false
        print('new random generation ',i,' of ', nr_it)
        vars = [random.choice([True, False]) for _ in range(nr_vars)]
        unsat_cls = set()
        evaluate_cls(cls,rel_cls,vars,expr_dict,unsat_cls,[])
        changed_bits = 0
        
        while changed_bits < 2*nr_vars*nr_vars:
            #print('--')
            if (len(unsat_cls)<36): #36 was chosen cause that is where nr_bits = len(unsat_cls)
                nr_bits = 1
            else:
                nr_bits = int(log(len(unsat_cls)))*10
            #print(nr_bits)
            changed_bits += nr_bits
            p_changes = modify_bits(unsat_cls,vars,nr_bits)
            evaluate_cls(cls,rel_cls,vars,expr_dict,unsat_cls,p_changes)
            #print('changed_bits,len(unsat_cls),nr_vars',changed_bits,len(unsat_cls),nr_vars)
            if (len(unsat_cls)==0):
                print('solution found!')
                return

    print('no solution found!')
    return

if __name__ == "__main__":
    file_name =  '2SATtest1.txt'

    start_time = time.time()

    with open(file_name, 'r') as f:
        nr_vars = int(f.readline().strip()) #nr_vars equals nr_clauses
        rel_cls = defaultdict(set)
        cls = []
        cl_idx = 0 #clause id gives index in clause list of the clause
        
        for line in f:
            c1, c2 = line.strip().split()
            c1, c2 = int(c1), int(c2)
            c1n, c2n = (c1<0), (c2<0) #booleans which store if c1 and c2 are negative
            p1, p2 = abs(c1)-1, abs(c2)-1
            cls.append((c1n,p1,c2n,p2))
            rel_cls[p1].add(cl_idx) #relevant clauses for position c1
            rel_cls[p2].add(cl_idx)
            cl_idx += 1

    run_Papadimitriou(nr_vars,cls,rel_cls) #nr_vars may be less than len(rel_cls) since some positions may not appear in any clause, those positions can be chosen randomly
    end_time = time.time()
    print(end_time - start_time)

    #test1 has a solution,


