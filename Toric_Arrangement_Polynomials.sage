class ToricArrangement(object):
    def __init__(self, m):
        '''
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: T
            <__main__.ToricArrangement object at 0x3359db950>
            sage: sage: T.poset_of_layers
            Finite poset containing 11 elements
            sage: T.dict
            {0: [0 0 1],
            1: [ 1 -1  1],
            2: [1 1 1],
            3: [  0   1 1/2],
            4: [0 1 1],
            5: [  1   0 1/2],
            6: [1 0 1],
            7: [  1   0 1/2]
            [  0   1 1/2],
            8: [  1   0   1]
            [  0   1 1/2],
            9: [  1   0 1/2]
            [  0   1   1],
            10: [1 0 1]
            [0 1 1]}
            
            BUGS:
            sage: m = matrix(QQ,2,3,[2,-1,1,2,1,1/2])
            '''
        #below defines the provate variables
        self.arr_mat = m
        self.poset_of_layers = poset_of_layers(m)
        self.dict = poset_dictionary(m)
        self.dim = m.ncols() - 1
    
    def characteristic_polynomial(self):
        '''
            TEST:
            sage: T.characteristic_polynomial()
            q^2 - 6*q + 8
            '''
        #the characteristic polynomial is defined on the dual of our poset
        pop = self.poset_of_layers.dual()
        return pop.characteristic_polynomial()

    def f_polynomial(self):
        '''
            OUTPUT: the f_polynomial of an arrangement
            
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: T.f_polynomial()
            8*q^2 + 12*q + 4
            
            ALGORITHM:
            We count the faces number of each dimension i in range [1,dim]
            Step1: For each i, construct a list of layers of dimension i
            Step2: For each layer of dimension i, count the number of
                dimension-i faces included.
            '''
        dim = self.arr_mat.ncols() - 1
        q = polygen(ZZ, 'q')
        res = 0
        for i in range(dim + 1):
            S = [i]
            temp = 0
            #follwoing count for the faces number of dimension i
            #chai is the list of layers of dimension i
            chai = self.flag_chain_of_layers(S)
            for c in chai:
                #here increase temp by the number of dim-i face
                #corresponding to each layer of dim i
                temp += self.num_chains_of_faces(c)
            #here temp count for f_i, the coefficient for q^i
            res += temp * q^i
        return res

    def h_polynomial(self):
        '''
            OUTPUT: return the h polynomial
        
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: T.h_polynomial()
            4*q + 4
            '''
        q = polygen(ZZ, 'q')
        f = self.f_polynomial()
        d = f.degree()
        #follwing comes from the definition of h polynomial
        f = (1 - q) ** d * f(q = q/(1-q))
        return q.parent(f)

        
    def flag_f_polynomial(self):
        '''
            OUTPUT:  the flag_f_polynomial of an arrangement
            
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: T.flag_f_polynomial()
            48*q0*q1*q2 + 24*q0*q1 + 24*q0*q2 + 24*q1*q2 + 4*q0 + 12*q1 + 8*q2
            
            ALGORITHM:
            We loop though each subset S of [n] to obtain the term \tilde{f}_S q_S
            Step1: For each S, collect all corresponding chains of layers
            Step2: For each chain of layer, collect all corresponding
                chains of faces
            '''
        n = self.arr_mat.ncols() - 1
        poly = PolynomialRing(ZZ, 'q', n+1)
        q = poly.gens()
        L = list_subsets_of_n(n)
        res = 0
        #each run of this loop, we add a term \tilde{f}_S q_S for res
        for S in L:
            #coeff count for the coefficient of q_S
            coeff = 0
            #chai is a list of all chain of layers corresponding to S
            chai = self.flag_chain_of_layers(S)
            for c in chai:
                #following increase coeff by the number of chains of faces
                #corresponding to each chain of layers
                coeff += self.num_chains_of_faces(c)
            #following construct temp as the term \tilde{f}_S q_S
            temp = coeff
            for i in S:
                temp *= q[i]
            res += temp
        return res

    def flag_h_polynomial(self):
        '''
            OUTPUT: the flag h_polynomial of an arrangement
            
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: T.flag_h_polynomial()
            8*q0*q1 + 12*q0*q2 + 4*q1*q2 + 4*q0 + 12*q1 + 8*q2
            
            '''
        n = self.arr_mat.ncols() - 1
        poly = PolynomialRing(ZZ, 'q', n+1)
        q = poly.gens()
        L = list_subsets_of_n(n)
        res = 0
        #following construct the flag h polynomial by a modified version of
        #our original formula (we put the product term inside summand
        #to avoid fraction)
        for S in L:
            coeff = 0
            chai = self.flag_chain_of_layers(S)
            for c in chai:
                coeff += self.num_chains_of_faces(c)
            temp = coeff
            #following represent what flag h polynomial is really doing:
            #change monomial q_S in flag f polynomial to be
            #\prod \limits_{i \in S}q_i \prod \limits_{i \notin S}(1-q_i)
            for i in S:
                temp *= q[i]
            for i in range(n + 1):
                if not i in S:
                    temp *= (1 - q[i])
            res += temp
        return res

    def cd_index(self):
        '''
            Return: a cd polynomial
            
            TEST:
            sage: m=matrix(QQ,3,3,[3,-1,1,1,-2,1,0,1,1/5])
            sage: T=ToricArrangement(m)
            sage: T.cd_index()
            8*c*d + 7*d*c
            sage: m = matrix(QQ,7,4,[1,0,0,1,0,1,0,1,0,0,1,1,1,0,0,1/2,0,1,0,1/2,0,0,1,1/2,1,1,1,1])
            sage: T = ToricArrangement(m)
            sage: T.cd_index()
            40*d^2 + 16*c^2*d + 28*c*d*c + 8*d*c^2
            '''
        s = self.str_ab_index()
        #Here we apply the second half of the formula in ERS09 Theorem 3.22
        cd = star_func(omega_func(a_s_b(H_prime(s))))
        F.<c,d> = FreeAlgebra(ZZ,2)
        return F(add_mult(cd))/2
    
    def cd_index_new_alg(self):
        '''
            TEST:
            sage: m = matrix(QQ,7,4,[1,0,0,1,0,1,0,1,0,0,1,1,1,0,0,1/2,0,1,0,1/2,0,0,1,1/2,1,1,1,1])
            sage: T = ToricArrangement(m)
            sage: T.cd_index_new_alg()
            40*d^2 + 16*c^2*d + 28*c*d*c + 8*d*c^2
            
            sage: m = matrix(QQ,3,3,[3,-1,1,-1,2,1,0,1,1/5])
            sage: T = ToricArrangement(m)
            sage: T.cd_index_new_alg()
            8*c*d + 7*d*c
            '''
        n = self.dim
        #cd_list is all posible cd monomial of degree n
        cd_list = possible_cd_str_of_n(n)
        #we use cd monomials to be the keys and construct a dictionary,
        #where the value indicate the coefficient for its key monomial
        cd_dict = {}
        #we let the default coefficient to be -1
        for i in cd_list:
            cd_dict[i] = -1
        #here need give initial coeff for some in cd_dict
        #we initial the coefficient for cd-monomial with only one d
        poly = PolynomialRing(ZZ, 'q', n+1)
        q = poly.gens()
        flag_h = self.flag_h_polynomial()
        #face_num is a list of face number where face_num[i] = f_i
        face_num = []
        for i in range(n + 1):
            face_num.append(flag_h[q[i]])
        #each loop bellow construct a cd monomial with only one d
        #and assign the value for that monomial in cd_dict
        #the coefficient for such monomial is showed in paper
        #as base case in recursion
        for k in range(n):
            temp = ''
            for i in range(k):
                temp += 'c'
            temp += 'd'
            for i in range(k + 1, n):
                temp += 'c'
            val = 0
            for i in range(k + 1):
                val += (-1)^(k - i)*face_num[i]
            cd_dict[temp] = val
        #above initialed cd strings with only one d

        #below each loop generate a binary string represent a monomial q_S
        #by loop through all \tilde{h}_S, we can obtain coefficients for all cd monomials
        #(see proof for this in paper)
        #by k in this range, we can generate all monomial q_S where S \subset [n]
        for k in range(1, 2^(n+1) - 1):
            #b is the binary string for k
            b = bin(k)
            b = b[2:]
            #b_str extend b to be a binary string of n+1 digit
            b_str = ''
            for i in range(n - len(b) + 1):
                b_str += '0'
            for i in range(len(b)):
                b_str += b[i]
            #b_list is a list of all possible cd monomials to use q_S as a term
            b_list = cd_str_for_bin(b_str)
            c = ''
            for i in range(len(b_str)):
                c += 'c'
            if c in b_list:
                b_list.remove(c)
            #below we use mono to construct the monomial q_S
            mono = 1
            for i in range(len(b_str)):
                if b_str[i] == '1':
                    mono *= q[i]
            #coeff = \tilde{h}_S
            coeff = flag_h[mono]
            #we use target to record the only cd monomial in b_list which doesn't have its coefficient yet
            #the sum count the sum of the coefficient for all other cd monomials in b_list
            #See the proof for there is at most one unkown cd monomial coefficient in b_list in paper
            target = ''
            sum = 0
            for s in b_list:
                if cd_dict[s] == -1:
                    target = s
                else:
                    sum += cd_dict[s]
            if not target == '':
                cd_dict[target] = coeff - sum
    
        #below need to construct free algebra form of the cd monomial from the dictionary
        F.<c,d> = FreeAlgebra(ZZ,2)
        res = 0
        for s in cd_list:
            temp = cd_dict[s]
            for i in range(len(s)):
                if s[i] == 'c': temp *= c
                else: temp *= d
            res += temp
        return res

#The following code are some helper functions to construct poset and polynomials
#ERS09 Algorithm
    def dual_with_empty_top(self):
        '''
            OUTPUT: the dual poset of poset of layers with a top element (empty face)
            
            TEST:
            sage: T = ToricArrangement(m)
            sage: T.poset_of_layers
            Finite poset containing 11 elements
            sage: T.dual_with_empty_top()
            Finite poset containing 12 elements
            
            sage: T = ToricArrangement(m)
            sage: T.poset_of_layers
            Finite poset containing 34 elements
            sage: T.dual_with_empty_top()
            Finite poset containing 35 elements
            '''
        #Get the cover relations from our poset of layers and its cardinality
        cover_relations = self.poset_of_layers.cover_relations()
        num_element = self.poset_of_layers.cardinality()
        vertex = list(range(0,num_element + 1))
        #Add some new cover relations: empty face is included in all the 0-faces
        dim_zero_elts = T.flag_chain_of_layers([0])
        for i in dim_zero_elts:
            i.insert(0,num_element)
        cover_relations.extend(dim_zero_elts)
        #Create a new poset with empty face and return its dual
        P = Poset([vertex,cover_relations],cover_relations=False)
        return P.dual()

    def str_ab_index(self):
        '''
            OUTPUT: an ab-string derived from the dual of poset of layers with a top (i.e.the empty face)
            
            TEST:
            sage: m=matrix(QQ,3,3,[3,-1,1,1,-2,1,0,1,1/5])
            sage: T=ToricArrangement(m)
            sage: T.str_ab_index()
            '6bb+2ba+6ab+aa'
            '''
        #Get the flag h-polynomial from the dual of poset of layers with top (i.e. empty face), split each term as a string and store them in a list
        P = self.dual_with_empty_top()
        from sage.combinat.posets.posets import Poset
        h = P.flag_h_polynomial()
        h_str = str(h)
        h_list = h_str.split('+')
        l = list(range(1,P.height()-1))
        new_h_list = []
        ab_list = []
        #Fix ' ' problem in string
        for i in h_list:
            if i[0] == ' ':
                new_h_list.append(i[1:])
            else:
                new_h_list.append(i)

        #First notice that we don't need the term x_i where i is the rank of the top element (i.e. empty face); then we run a loop in new_h_list: if x_i is in the term, we add a 'b'; if not, we add an 'a'; finally we append our ab-string for each term to a new list called ab_list
        for i in new_h_list:
            t = split_string(i)
            s = t[0]
            for j in l:
                if 'x'+ str(j) in i:
                    s = s + 'b'
                else:
                    s = s + 'a'
            ab_list.append(s)
        #Return the ab polynomial as a string
        return get_string_from_list(ab_list)

    def num_chains_of_faces(self, C):
        '''
            INPUT: C, a list of integers, representing a chain
            OUTPUT: number of chains of faces corresponding to C
        
            NOTE: this function serves for flag f_polynomial
        
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: C = [0,10]
            sage: T.num_chains_of_faces(C)
            8
            '''
            #The following code works for cases fullfill our requirement
            
        p = self.poset_of_layers
        res = 1
        #sub is all elements in the poset of layers below C[0]
        sub = p.principal_order_ideal(C[0])
        #subp is the subposet below C[0]
        subp = p.subposet(sub)
        #but plug 0 into poly, we obtain the number of faces corresponding to C[0]
        poly = subp.dual().characteristic_polynomial()
        res *= abs(poly(0))
        #following each loop we construct a subposet between interval [c[i],c[i+1]]
        #by plug in -1 to its characteristic polynomial, we obtain the number of chains in the poset of faces corresponding to c[i]>c[i+1] in the poset of layers
        for i in range(len(C) - 1):
            itv = p.closed_interval(C[i], C[i + 1])
            subp = p.subposet(itv)
            poly = subp.dual().characteristic_polynomial()
            res *= abs(poly(-1))
        return res

    def flag_chain_of_layers(self,S):
        '''
            INPUT: S \subset [n]
            OUTPUT: return a set of chains. Each chain is a tuple representing
            a chain of layers corresponding to S.
        
            NOTE: this function serves for flag f_polynomial
        
            TEST:
            sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
            sage: T = ToricArrangement(m)
            sage: S
            [0, 2]
            sage: c = T.flag_chain_of_layers(S)
            sage: c
            [[10, 0], [9, 0], [8, 0], [7, 0]]
            
            ALGORITHM:
            Step1: collect all elements in the poset of layers with dimension in S
            Step2: construct a new poset using above elements ordered by inclusion
            Step3: use build in functions to obtain a list of chains in that subposet
            '''
        dim = self.arr_mat.ncols() - 1
        sset = set(())
        t = {}
        for k in S:
            sset.add(k)
        #following we collect all elements in self.dict with dimension in S
        #put the qualified elements with its original label of vertex
        for i in self.dict:
            m = self.dict[i]
            if dim - rank(charact_part(m)) in sset:
                t[i] = m
        cmp_fn = lambda p,q: is_subtorus(t[p],t[q])
        from sage.combinat.posets.posets import Poset
        #subp is the subposet with all elements having dimension in S
        subp = Poset((t, cmp_fn))
        #C is all chains of layers we want
        C = subp.chains()
        res = list(C.elements_of_depth_iterator(len(S)))
        return res

#FOLLOWING CODE IS NOT IN THE DECLARATION OF TORICARRANGEMENT CLASS
#The following code are some useful functions
def check_qualification(m):
    '''
        return if we can use our algorithm to calculate flag f_polynomial
        
        TEST:
        sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
        sage: m
        [ 2  0  1]
        [ 0  2  1]
        [ 1  1  1]
        [ 1 -1  1]
        sage: check_qualification(m)
        True
        
        sage: m = matrix(QQ,2,3,[2,-1,1,2,1,1/2])
        sage: m
        [  2  -1   1]
        [  2   1 1/2]
        sage: check_qualification(m)
        False
        
        sage: m = matrix(QQ,3,3,[1,0,1,0,1,1,2,-1,1])
        sage: m
        [ 1  0  1]
        [ 0  1  1]
        [ 2 -1  1]
        sage: check_qualification(m)
        False
        
        sage: m = matrix(QQ,4,3,[1,0,1,1,0,1/2,0,1,1,0,1,1/2])
        sage: m
        [  1   0   1]
        [  1   0 1/2]
        [  0   1   1]
        [  0   1 1/2]
        sage: check_qualification(m)
        True
        '''
    c = charact_part(m)
    dim = m.ncols() - 1
    if rank(c) < dim: return false
    categ = []
    for i in range(c.nrows()):
        categ.append(-1)
    #the ith elt of categ mark if c[i] belongs to some category already
    curr = 0
    #curr mark which category should the next independent vector be
    #curr should be at most dim - 1
    count = []
    #count[i] record #of element in ith category
    #count should be at most dim - 1 long
    for i in range(c.nrows()):
        if categ[i] == -1:
            #meaning c[i] is not discovered before
            categ[i] = curr
            num = gcd(c[i])
            for j in range(i + 1, c.nrows()):
                #now see if i and j are parallel
                tl = []
                for k in range(c.ncols()):
                    tl.append(c[i][k])
                for k in range(c.ncols()):
                    tl.append(c[j][k])
                temp = matrix(QQ,2,c.ncols(),tl)
                tl = []
                if rank(temp) == 1:#m[j] is parallel with m[i]
                    categ[j] = categ[i]
                    num += gcd(c[j])
            count.append(num)
            curr += 1
    ind = 0
    for i in count:
        if i >= 2: ind += 1
    if ind < dim: return false
    return true

#The following code are some helper functions
#Helper functions for cd-index
def list_subsets_of_n(n):
    '''
        OUTPUT: all nonempty subset of n
        
        TEST:
        sage: l = list_subsets_of_n(5)
        sage: len(l)
        31
        '''
    #base case for recursive algorithm
    if n == 0:
        return [[0]]
    else:
        #let l be all subsets of n-1
        l = list_subsets_of_n(n - 1)
        #fitst collect all elements in l in our result representing all subsets of [n] without n
        res = l
        #now collect all subsets of [n] with n
        for i in range(len(l)):
            temp = []
            for j in l[i]:
                temp.append(j)
            temp.append(n)
            res.append(temp)
        res.append([n])
    res.sort()
    return res

def add_mult(s):
    '''
        Input: a cd polynomial with each term a cd-string
        Return: a cd polynomial adding '*' to each term
        
        TEST:
        sage: s = str('12ccd+2cdc+24dd')
        sage: add_mult(s)
        '12*c*c*d+2*c*d*c+24*d*d'
        '''
    #split ab polynomial by '+' and store each term in a list
    s = s.split('+')
    cd_poly = []
    #add '*' between each 'c'/'d' variable and return a polynomial-like string
    for i in s:
        t = split_string(i)
        cd = t[0]
        for j in t[1]:
            cd += '*'
            cd += j
        cd_poly.append(cd)
    return get_string_from_list(cd_poly)

def a_s_b(s):
    '''
        Input: an ab polynomial
        Return: an ab polynomial adding 'a' in the front and 'b' in the back for each term
        
        TEST:
        sage: s = str('12abbaa+8abaaa+9aabba+2aaaaa')
        sage: a_s_b(s)
        '12aabbaab+8aabaaab+9aaabbab+2aaaaaab'
        '''
    #split ab polynomial by '+' and store each term in a list
    s = s.split('+')
    adding_a_b = []
    for i in s:
        #for each term, we split the number part and variable part
        t = split_string(i)
        #add an 'a' in the front and 'b' in the back and append to the new list
        adding_a_b.append(t[0] + 'a' + t[1] + 'b')
    #return a polynomial-like string
    return get_string_from_list(adding_a_b)

def omega_func(s):
    '''
        Input: an ab polynomial
        Return: a polynomial replacing each 'ab' with '2d' and other letters with 'c'
        TEST:
        sage: s = str('12abbaa+8abaaa+9aabba+2aaaaa')
        sage: omega_func(s)
        '24dccc+16dccc+18cdcc+2ccccc'
        '''
    #split ab polynomial by '+' and store each term in a list
    s = s.split('+')
    cd_string = []
    for i in s:
        cd_term = ''
        #for each term, we split the number part and variable part
        t = split_string(i)
        #check if there is no variable part
        if t[0] == '':
            t0 = 1
        else:
            t0 = int(t[0])
        j = 0
        #replace each 'ab' with '2d' and other letters with 'c' and append the result to the new list
        while j < len(t[1]):
            if j < len(t[1]) - 1 and t[1][j] + t[1][j+1] == 'ab':
                cd_term += 'd'
                t0 *= 2
                j += 2
            else:
                cd_term += 'c'
                j += 1
        cd_string.append(str(t0) + cd_term)
    #return a polynomial-like string
    return get_string_from_list(cd_string)

def H_prime(s):
    '''
        Input: an ab polynomial
        Return: a polynomial with last letter removed for each term
        
        TEST:
        sage: s = str('ab+ba')
        sage: s
        'ab+ba'
        sage: H_prime(s)
        'a+b'
        
        sage: s = str('abbaa+abaaa+aabba+aaaaa')
        sage: s
        'abbaa+abaaa+aabba+aaaaa'
        sage: H_prime(s)
        'abba+abaa+aabb+aaaa'
        
        sage: s = str('7abba')
        sage: H_prime(s)
        '7abb'
        '''
    #split ab polynomial by '+' and store each term in a list
    s = s.split('+')
    last_removed = []
    for i in s:
        #for each term, we split the number part and variable part
        t = split_string(i)
        #remove the last letter of the variable part if the variable part exists
        if len(t[1]) > 1:
            last_removed.append(t[0] + t[1][:-1])
    #return a polynomial-like string
    return get_string_from_list(last_removed)

def star_func(s):
    '''
        Input: an ab polynomial
        Return: a polynomial with ab-part order reversed
        
        TEST:
        sage: s = str('abbaa+abaaa+aabba+aaaaa')
        sage: star_func(s)
        'aabba+aaaba+abbaa+aaaaa'
        
        sage: s = str('12abbaa+8abaaa+9aabba+2aaaaa')
        sage: star_func(s)
        '12aabba+8aaaba+9abbaa+2aaaaa'
        '''
    #split ab polynomial by '+' and store each term in a list
    s = s.split('+')
    reversed = []
    for i in s:
        #for each term, we split the number part and variable part
        t = split_string(i)
        #reverse the ab-variable part and append the result to a new list
        reversed.append(t[0] + t[1][::-1])
    #return a polynomial-like string
    return get_string_from_list(reversed)

def get_string_from_list(l):
    '''
        Input: a list of strings where each string is a term of a polynomial
        Return: a string of polynomial
        
        TEST:
        l = ['ab', 'ba', 'aa']
        sage: get_string_from_list(l)
        'ab+ba+aa'
        '''
    s = ''
    #add a '+' between each term and form a polynomial-like string
    for i in l:
        s += i
        s += '+'
    s = s[:-1]
    return s

def check_number(s):
    '''
        Return true if the first element of the string is a number
        '''
    result = False
    if s[0] == '0' or s[0] == '1' or s[0] == '2' or s[0] == '3' or s[0] == '4' or s[0] == '5' or s[0] == '6' or s[0] == '7' or s[0] == '8' or s[0] == '9':
        result = True
    return result

def split_string(s):
    '''
        Seperate the number part and the letter part and return a tuple
        
        TEST:
        sage: s = str('22ab')
        sage: split_string(s)
        ('22', 'ab')
        sage: s = str('7aabba')
        sage: split_string(s)
        ('7', 'aabba')
        '''
    num = ''
    while check_number(s):
        num += s[0]
        s = s[1:]
    return (num, s)

#Our new algorithm
def possible_cd_str_of_n(n):
    '''
        given dimension n, output all possible cd strings
        
        TEST:
        sage: possible_cd_str_of_n(5)
        ['ccdcc',
        'dccd',
        'cdccc',
        'cdcd',
        'ccdd',
        'ccccd',
        'cddc',
        'ddcc',
        'ddd',
        'dcdc',
        'dcccc',
        'cccdc']
        '''
    #d has degree 2, c has degree 1, we want to come up with all cd monomials of degree n
    #the pure c monomial is removed since it can't appear in the cd-index form of flag h-polynomial
    
    #base case for recursive algorithm
    if n == 0: return ['c']
    if n == 1: return ['d', 'cc']
    S = set()
    l1 = possible_cd_str_of_n(n - 1) #should insert 'c' inside
    l2 = possible_cd_str_of_n(n - 2) #should insert 'd' inside
    #l1 is a list of cd monomial with degree n-1, we insert 'c' into all possible position
    for i in l1:
        for j in range(len(i)):
            temp = str_insert(i,j,'c')
            S.add(temp)
    #l2 is a list of cd monomial with degree n-1, we insert 'd' into all possible position
    for i in l2:
        for j in range(len(i)):
            temp = str_insert(i,j,'d')
            S.add(temp)
    #above we used S to collect all monomials in order to remove duplication
    res = []
    #following we collect all elements in S into a list res[]
    c = ''
    for i in range(n + 1):
        c += 'c'
    for s in S:
        res.append(s)
    #remove the pure c monomial in res[]
    if c in res:
        res.remove(c)
    return res

def str_insert(s,i,c):
    '''
        TEST:
        sage: s = 'abcde'
        sage: str_insert(s,3,'g')
        'abcgde'
        
        sage: s = 'abc'
        sage: str_insert(s,3,'g')
        'abcg'
        '''
    temp = ''
    for k in range(i):
        temp += s[k]
    temp += c
    for k in range(i, len(s)):
        temp += s[k]
    return temp

def cd_str_for_bin(b):
    '''
        sage: s = '101'
        sage: cd_str_for_bin(s)
        ['dc', 'ccc', 'cd']
        sage: s = '10101'
        sage: cd_str_for_bin(s)
        ['cdd', 'ccdc', 'dcd', 'cdcc', 'dccc', 'cccd', 'ddc', 'ccccc']
        '''
    #base cases for recursive algorithm
    if b == '0' or b == '1': return ['c']
    if b == '01' or b == '10': return ['d', 'cc']
    res = []
    S = set()
    n = len(b)
    #if b[0] != b[1], we can replace the first two digits by a 'd'
    if b[0] != b[1]:
        tail = b[2:]
        #call cd_str_for_bin recursively, l is the list of all possible cd-monomial after remove the first two digit of b, then we add a 'd' to the front of all elements in l
        l = cd_str_for_bin(tail)
        for i in l:
            S.add(str_insert(i,0,'d'))
            S.add(str_insert(str_insert(i,0,'c'),0,'c'))
    #we can always replace the first digit by a 'c'
    tail = b[1:]
    l = cd_str_for_bin(tail)
    for i in l:
        S.add(str_insert(i,0,'c'))
    #if the last two digits of b is different, we are allowed to replace the last two digit by a 'd'
    if b[n - 1] != b[n - 2]:
        pre = b[:-2]
        l = cd_str_for_bin(pre)
        for i in l:
            S.add(str_insert(i,len(i),'d'))
            S.add(str_insert(str_insert(i,len(i),'c'),len(i) + 1,'c'))
    #we can always replace the last digit by 'c'
    pre = b[:-1]
    l = cd_str_for_bin(pre)
    for i in l:
        S.add(str_insert(i,len(i),'c'))
    for i in S:
        res.append(i)
    return res

#Helper functions for constructing poset of layers
def poset_of_layers(m):
    '''
        sage: m = matrix([[1,0,1],[0,1,1]])
        sage: m
        [1 0 1]
        [0 1 1]
        sage: P = poset_of_layers(m)
        sage: P
        Finite poset containing 4 elements
        
        sage: m = matrix(QQ,2,3,[1,-1,1,1,1,1])
        sage: m
        [ 1 -1  1]
        [ 1  1  1]
        sage: P = poset_of_layers(m)
        sage: P
        Finite poset containing 5 elements
        
        sage: m = matrix(QQ,3,3,[2,-1,1,1,0,1,0,1,1])
        sage: m
        [ 2 -1  1]
        [ 1  0  1]
        [ 0  1  1]
        sage: P = poset_of_layers(m)
        sage: P
        Finite poset containing 6 elements
        
        sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
        sage: m
        [ 2  0  1]
        [ 0  2  1]
        [ 1  1  1]
        [ 1 -1  1]
        sage: P = poset_of_layers(m)
        sage: P
        Finite poset containing 11 elements
        '''
    #t is the dictionary collecting all elements in the poset of layers
    t = poset_dictionary(m)
    #order the elements in the poset by inclusion
    cmp_fn = lambda p,q: is_subtorus(t[p],t[q])
    from sage.combinat.posets.posets import Poset
    return Poset((t, cmp_fn))

def poset_dictionary(m):
    '''
        TEST:
        sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
        sage: m
        [ 2  0  1]
        [ 0  2  1]
        [ 1  1  1]
        [ 1 -1  1]
        sage: t = poset_dictionary(m)
        sage: t
        {0: [0 0 1],
        1: [ 1 -1  1],
        2: [1 1 1],
        3: [  0   1 1/2],
        4: [0 1 1],
        5: [  1   0 1/2],
        6: [1 0 1],
        7: [  1   0 1/2]
        [  0   1 1/2],
        8: [  1   0   1]
        [  0   1 1/2],
        9: [  1   0 1/2]
        [  0   1   1],
        10: [1 0 1]
        [0 1 1]}
        '''
    l = list_of_conn_comp(m)
    p_elt  = poset_element(l)
    L = []
    dim = m.ncols() - 1
    wl = []
    #use matrix [0,...,0,1] to represent the whole space T = (S^1)^n
    for i in range (0, dim):
        wl.append(0)
    wl.append(1)
    whole_space = matrix(QQ, 1, len(wl), wl)
    L.append(whole_space)
    #append L by the connected components of all intersections in p_elt
    for i in p_elt:
        if intersection_exist(i):
            temp = conn_comp_intersection(i)
            L = L + temp
    #use rem_dup to collect all elements in L after remove duplication
    rem_dup = []
    for i in L:
        exist = false
        for j in rem_dup:
            if is_subtorus(i, j) and is_subtorus(j, i):
                exist = true
        if not exist:
            rem_dup.append(i)
    #construct the dictionary for rem_dup which is the final elements in the poset of layers
    t = {}
    for i in range(len(rem_dup)):
        t[i] = rem_dup[i]
    return t

def dict_find_key(t, m):
    '''
        TEST:
        sage: m = matrix(QQ,3,3,[2,-1,1,1,0,1,0,1,1])
        sage: m
        [ 2 -1  1]
        [ 1  0  1]
        [ 0  1  1]
        sage: P = poset_of_layers(m)
        sage: P
        Finite poset containing 6 elements
        sage: t = poset_dictionary(m)
        sage: t
        {0: [0 0 1], 1: [0 1 1], 2: [1 0 1], 3: [ 2 -1  1], 4: [1 0 1]
        [0 1 1], 5: [  1   0 1/2]
        [  0   1   1]}
        sage: m1 = matrix(QQ,2,3,[1,0,1/2,0,1,1])
        sage: m1
        [  1   0 1/2]
        [  0   1   1]
        sage: i = dict_find_key(t, m1)
        sage: i
        5
        '''
    for i in t:
        if t[i] == m:
            return i;
    return -1

def poset_element(l):
    '''
        TEST:
        sage: m = matrix(QQ,3,4,[3,6,9,1,0,4,6,1,0,0,4,1])
        sage: m
        [3 6 9 1]
        [0 4 6 1]
        [0 0 4 1]
        sage: l = list_of_conn_comp(m)
        sage: l
        [[[1, 2, 3, 1/3], [1, 2, 3, 2/3], [1, 2, 3, 1]],
        [[0, 2, 3, 1/2], [0, 2, 3, 1]],
        [[0, 0, 1, 1/4], [0, 0, 1, 1/2], [0, 0, 1, 3/4], [0, 0, 1, 1]]]
        sage: k = poset_element(l)
        sage: len(k)
        59
        
        sage: m = matrix(QQ,2,3,[1,-1,1,1,1,1])
        sage: l = list_of_conn_comp(m)
        sage: l
        [[[1, -1, 1]], [[1, 1, 1]]]
        sage: k = poset_element(l)
        sage: k
        [
        [ 1 -1  1]
        [1 1 1], [ 1 -1  1], [ 1  1  1]
        ]
        
        ALGORITHM:
        This is a recursive algorithm to return all possible intersection of a poset
        Step1: remove the last hypertori (last row of l)
        Step2: call poset_element recursively to obtain all possible intersection for all other hypertori, obtain a list pre.
        Step3: for each element in pre, intersect with all connected components in the last hypertori to obtain a list of new intersections, return this list append all connected components in the last hypertorus and all elements in pre.
        '''
    res = []
    #base case for recursion
    if len(l) == 1:
        return matrices_from_nested_list(l)
    #remove and record the last hypertori
    last_row = l.pop(len(l) - 1)
    l_last = matrices_from_nested_list([last_row])
    #pre is the list of all possible intersection for the rest of hypertori
    pre = poset_element(l)
    #append list with the singleton of connected components in the last hypertorus and append res with all intersections without the last hypertorus
    res = res + l_last
    res = res + pre
    #intersect each intersection in pre with one connected components in the last hypertorus
    for i in l_last:
        for j in pre:
            temp = matrix_append_row(j, i)
            res.append(temp)
    return res

def conn_comp_intersection(m):
    '''
        INPUT: a matrix with multiple rows representing an intersection
        
        OUTPUT: a list of matrices representing the connected component of
        the input intersection
        
        TEST:
        sage: m = matrix(QQ,2,3,[1,-1,1,1,1,1])
        sage: m
        [ 1 -1  1]
        [ 1  1  1]
        sage: c = conn_comp_intersection(m)
        sage: c
        [
        [  1   0 1/2]  [1 0 1]
        [  0   1 1/2], [0 1 1]
        ]
        
        sage: m = matrix(QQ,2,4,[3,6,9,1,0,4,6,1])
        sage: m
        [3 6 9 1]
        [0 4 6 1]
        sage: c = conn_comp_intersection(m)
        sage: c
        [
        [  1   0   0 5/6]  [  1   0   0 1/6]  [1 0 0 1]  [  1   0   0 1/3]
        [  0   2   3 1/2], [  0   2   3 1/2], [0 2 3 1], [  0   2   3   1],
        
        [  1   0   0 1/2]  [  1   0   0 2/3]
        [  0   2   3 1/2], [  0   2   3   1]
        ]
        
        sage: m = matrix(QQ,2,3,[2,-1,1,1,1,1])
        sage: m
        [ 2 -1  1]
        [ 1  1  1]
        sage: c = conn_comp_intersection(m)
        sage: c
        [
        [  1   0 1/3]  [  1   0 2/3]  [1 0 1]
        [  0   1 2/3], [  0   1 1/3], [0 1 1]
        ]
        
        sage: m = matrix(QQ,4,3,[2,0,1,0,2,1,1,1,1,1,-1,1])
        sage: m
        [ 2  0  1]
        [ 0  2  1]
        [ 1  1  1]
        [ 1 -1  1]
        sage: c = conn_comp_intersection(m)
        sage: c
        [
        [  1   0 1/2]  [1 0 1]
        [  0   1 1/2], [0 1 1]
        ]
        
        sage: m1 = matrix(QQ,3,3,[1,2,1,3,4,1/2,1,2,1/3])
        sage: m1
        [  1   2   1]
        [  3   4 1/2]
        [  1   2 1/3]
        sage: c = conn_comp_intersection(m1)
        sage: c
        []
        '''
    res = []
    if not intersection_exist(m):
        return res
    #here separate each hypertorus in m to be a list of connected components
    l = list_of_conn_comp(m)
    k = matrices_from_nested_list(l)
    #unimodulized k
    pre_res = matrix_list_unimodulize(k)
    #use S to remove the duplicated matrix in k
    S = set(())
    for k in pre_res:
        if (intersection_exist(k)):
            k.set_immutable()
            S.add(k)
    for k in S:
        res.append(k)
    return res

def matrix_list_unimodulize(L):
    '''
        INPUT: L is a list of matrix
        
        OUTPUT: a list of unimodular matrix
        
        TEST:
        sage: m1 = matrix(QQ,2,4,[1,2,3,1,0,4,6,1])
        sage: m2 = matrix(QQ,2,4,[1,2,-1,2,0,1,1,1])
        sage: M = [m1,m2]
        sage: M
        [
        [1 2 3 1]  [ 1  2 -1  2]
        [0 4 6 1], [ 0  1  1  1]
        ]
        sage: K = matrix_list_unimodulize(M)
        sage: K
        [
        [  1   0   0 1/2]  [1 0 0 1]  [ 1  0 -3  1]
        [  0   2   3 1/2], [0 2 3 1], [ 0  1  1  1]
        ]
        sage: is_unimodular(K[0])
        True
        sage: is_unimodular(K[1])
        True
        sage: is_unimodular(K[2])
        True
        '''
    res = []
    #below each loop, we want to change an element in L to be a list of its connected components in unimodular form
    for m in L:
        #temp_ech is the integer echelon form of m
        temp_ech = trace_integer_echelon(m)
        #if temp-ech is connected we append it to res
        if is_unimodular(temp_ech):
            res.append(temp_ech)
        #if not, we separate temp_ech to be a list of connected component temp_l
        #call matrix_list_unimodulize recursively to unimodulize it
        #and append its unimodular form to res
        else:
            temp_l = list_of_conn_comp(temp_ech)
            temp_k = matrices_from_nested_list(temp_l)
            res = res + matrix_list_unimodulize(temp_k)
    return res


def trace_integer_echelon(m):
    '''
        trying new way to implement integer_echelon
        
        sage: m = matrix(ZZ,4,3,[2,0,1,0,2,1,1,-1,1,1,1,1])
        sage: m
        [ 2  0  1]
        [ 0  2  1]
        [ 1 -1  1]
        [ 1  1  1]
        sage: t = trace_integer_echelon(m)
        sage: t
        [1 1 1]
        [0 2 1]
        
        '''
    #we need append a ext_col x ext_col identity matrix to trace the row operations
    ext_col = m.nrows()
    char_m = charact_part(m)
    #l_trace collect the elements used in m_trace
    l_trace = []
    for i in range(char_m.nrows()):
        for j in range(char_m.ncols()):
            l_trace.append(m[i][j])
        for k in range(0, i):
            l_trace.append(0)
        l_trace.append(1)
        for k in range(i + 1, ext_col):
            l_trace.append(0)
    #m_trace is the matrix we obtained after appending extra identity matrix after char_m
    #here m_trice is defined on integer ring to get integer echelon form
    m_trace = matrix(ZZ,m.nrows(),char_m.ncols() + ext_col, l_trace)
    #now the append part give us the clue for row operations
    int_ech_trace = m_trace.echelon_form()
    l_int = []
    for i in char_m:
        for j in i:
            l_int.append(j)
    #char_m_int is the characteristic part of m over integer ring
    char_m_int = matrix(ZZ, char_m.nrows(),char_m.ncols(),l_int)
    char_m_ech = char_m_int.echelon_form()
    #const is a list collecting all constant term in the last column
    const = []
    #each loop will count for the constant for the ith row of m
    for i in range(char_m.nrows()):
        #tamp_const indicate the constant for the ith row of m
        temp_const = 0
        #each loop below, we count the number of multiples of the kth row in m to be used
        #to form the ith row in the echelon form of char_m
        for k in range(ext_col):
            temp_const += m[k][char_m.ncols()] * int_ech_trace[i][char_m.ncols() + k]
        #below we restrict each constant to be in range (0,1]
        while temp_const <= 0:
            temp_const += 1
        while temp_const > 1:
            temp_const -= 1
        const.append(temp_const)
    res = matrix_append_column(char_m_ech, const)
    rk = rank(char_m)
    #below we erase all rows with 0 vector as characteristic part
    res = matrix_erase_rows(res, rk)
    return res

def intersection_exist(m):
    '''
        INPUT: a matrix
        
        OUTPUT: return a boolean value indicating if the intersection exists
        (just need to see if some torus in m is parellal but not the same)
        
        TEST:
        sage: m1 = matrix(QQ,3,3,[1,2,1,3,4,1/2,1,2,1/3])
        sage: m1
        [  1   2   1]
        [  3   4 1/2]
        [  1   2 1/3]
        sage: intersection_exist(m1)
        False
        sage: m1 = m1 = matrix(QQ,3,3,[1,2,1,3,4,1/2,1,2,1])
        sage: m1
        [  1   2   1]
        [  3   4 1/2]
        [  1   2   1]
        sage: intersection_exist(m1)
        True
        
        NOTE: if two hypertori is not parrelel, they must have at least one intersection
        The only case for a matrix representing empty intersection is that some hypertori
        inside is parallel with each other but not the same
        
        '''
    char_m = charact_part(m)
    #following loop verify if m[i] and m[j] has the same characteristic part but different constant term
    #in which case, intersection does not exists
    for i in range(m.nrows()):
        for j in range(i + 1, m.nrows()):
            if char_m[i] == char_m[j] and m[i][m.ncols() - 1] != m[j][m.ncols() - 1]:
                return false;
    return true

def new_is_subtorus(m1, m2):
    '''
        TEST:
        sage: m1 = matrix(QQ,2,4,[1,0,0,1,0,2,3,1])
        sage: m2 = matrix(QQ,2,4,[1,0,0,1/2,0,2,3,1/2])
        sage: new_is_subtorus(m1, m2)
        False
        sage: m2 = matrix(QQ,1,4,[1,0,0,1])
        sage: new_is_subtorus(m1, m2)
        True
        '''
    if not is_unimodular(m1) or not is_unimodular(m2):
        print("Inout unimodular matrix!")
        return false
    m1 = trace_integer_echelon(m1)
    m2 = trace_integer_echelon(m2)
    V = ZZ^(m1.ncols() - 1)
    
    m1_int = charact_part(m1)
    m1_int = m1_int.change_ring(ZZ)
    m1_int_list = matrix_to_list(m1_int)
    
    m2_int = charact_part(m2)
    m2_int = m2_int.change_ring(ZZ)
    m2_int_list = matrix_to_list(m2_int)
    
    W1 = V.submodule(m1_int_list)
    W2 = V.submodule(m2_int_list)
    
    if not W2.is_submodule(W1):
        return false

    for i in range(len(m2_int_list)):
        coord = W1.coordinates(m2_int_list[i])
        temp = 0
        for j in range(len(coord)):
            temp += coord[j] * m1[i][m1.ncols()-1]
        if not temp == m2[i][m2.ncols()-1]:
            return false

    return true

def is_subtorus(m1, m2):
    '''
        Input: two matrices indicating two connected intersections
        Note that they are all primitive
        Output: return true if m1 is a subtorus of m2

        TEST:
        sage: m1 = matrix(QQ,2,4,[1,2,3,1,4,5,6,1])
        sage: m2 = matrix(QQ,1,4,[1,2,3,1])
        sage: m1
        [1 2 3 1]
        [4 5 6 1]
        sage: m2
        [1 2 3 1]
        sage: is_subtorus(m1,m2)
        True
        sage: is_subtorus(m2,m1)
        False

        sage: m1 = matrix(QQ,3,3,[4,5,6,1,2,3,7,8,9])
        sage: m2 = matrix(QQ,2,3,[7,8,9,1,2,3])
        sage: m1
        [4 5 6]
        [1 2 3]
        [7 8 9]
        sage: m2
        [7 8 9]
        [1 2 3]
        sage: is_subtorus(m1,m2)
        True
        sage: is_subtorus(m2,m1)
        False

        '''
    V = ZZ^(m1.ncols() - 1)

    m1_int = charact_part(m1)
    m1_int = m1_int.change_ring(ZZ)
    m1_int_list = matrix_to_list(m1_int)

    m2_int = charact_part(m2)
    m2_int = m2_int.change_ring(ZZ)
    m2_int_list = matrix_to_list(m2_int)

    W1 = V.submodule(m1_int_list)
    W2 = V.submodule(m2_int_list)

    if not W2.is_submodule(W1):
        return false
    #in case we can't have a solution, since we only solved the equation in real number
    try:
        p = point_of_subtorus(m1)
    except:
        return false
    l = m2.ncols()

    for n in m2:
        #see if that point in m1 in also in m2
        multiplication = p[0]^n[0]
        for i in range(1,l - 1):
            multiplication *= (p[i] ^ n[i])
        if not multiplication == e ^ (2 * pi * I * n[l - 1]):
            return false

    return true

def point_of_subtorus(m):
    '''
        Input: a matrix represent a subtorus
        Output: a point in the subtorus (as a vector)
        
        TEST:
        sage: m1=matrix(QQ,2,3,[1,2,1,2,1,1])
        sage: m1
        [1 2 1]
        [2 1 1]
        sage: point_of_subtorus(m1)
        [e^(2/3*pi), e^(2/3*pi)]
        '''
    
    b = m.column(m.ncols()-1)
    A = charact_part(m)
    #first solve the equation in R^n
    v = A.solve_right(b)
    l = []
    for x in v:
        l.append(e ^ (2 * pi * I * x))
    return l

def list_of_conn_comp(m):
    '''
        INPUT: a matrix (a toric arrangement)
        OUTPUT: a list of nested list
        l[i], a nested list, represents the connected component of m[i]
        
        TEST:
        sage: m = matrix(QQ, 2, 4, [3,6,9,1,0,4,6,1])
        sage: m
        [3 6 9 1]
        [0 4 6 1]
        sage: l = list_of_conn_comp(m)
        sage: l
        [[[1, 2, 3, 1/3], [1, 2, 3, 2/3], [1, 2, 3, 1]],
        [[0, 2, 3, 1/2], [0, 2, 3, 1]]]
        
        sage: m = matrix(QQ,3,4,[3,6,9,1,0,4,6,1,0,0,4,1])
        sage: m
        [3 6 9 1]
        [0 4 6 1]
        [0 0 4 1]
        sage: l = list_of_conn_comp(m)
        sage: l
        [[[1, 2, 3, 1/3], [1, 2, 3, 2/3], [1, 2, 3, 1]],
        [[0, 2, 3, 1/2], [0, 2, 3, 1]],
        [[0, 0, 1, 1/4], [0, 0, 1, 1/2], [0, 0, 1, 3/4], [0, 0, 1, 1]]]
        
        '''
    l = []
    #each loop will append l with a nested list
    #l[i] represent a list of all connected components of m[i]
    for i in range(0, m.nrows()):
        #temp collect the ith row of m
        temp = []
        for j in m[i]:
            temp.append(j)
        tl = [temp]
        ma = list_to_matrix(tl)
        k = conn_comp_torus(ma)
        l.append(k)
    return l

def is_unimodular(m):
    '''
        we should only verify if the matrix
        formed by removing the last column of m is unimodular
        this function is really seeing if a layer has only one connected component
        
        TEST:
        sage: m = matrix(QQ,2,4,[1,2,3,1,0,4,6,1])
        sage: m
        [1 2 3 1]
        [0 4 6 1]
        sage: is_unimodular(m)
        False
        sage: m = matrix(QQ,2,4,[1,2,3,1,0,2,3,1])
        sage: m
        [1 2 3 1]
        [0 2 3 1]
        sage: is_unimodular(m)
        True
        sage: m = matrix(QQ,2,4,[1,2,3,1,0,2,3,1/2])
        sage: m
        [  1   2   3   1]
        [  0   2   3 1/2]
        sage: is_unimodular(m)
        True
        
        ALGORITHM:
        This comes from a theorhm in...
        '''
    m = charact_part(m)
    r = m.rank()
    m = m.minors(r)
    d = gcd(m)
    return abs(d) == 1

def conn_comp_torus(m):
    '''
        m should be a single torus,
        this function will return the connected component of m as a list of torus
        (matrix with only one row)
        Say if the constant is c, it represents e^{2\pi c}
        
        TEST:
        sage: m = matrix(QQ, [0,4,6,1])
        sage: r = conn_comp_torus(m)
        sage: r
        [[0, 2, 3, 1/2], [0, 2, 3, 1]]
        
        sage: m = matrix(QQ,1,3,[0,2,1/2])
        sage: m
        [  0   2 1/2]
        sage: r = conn_comp_torus(m)
        sage: r
        [[0, 1, 3/4], [0, 1, 1/4]]
        
        ALGORITHM:
        For a single torus m not being primitive, it has different connected components.
        We want to recover the nested list form representing several hypertori,
        each representing a connected component of m
        Step1:
        '''
    c = matrix_to_list(m)
    c = flatten(c)
    #we first remove the constant term
    c.pop(len(c) - 1)
    #d shows how many connected components should m have
    d = gcd(c)
    if d == 0: return m
    #we edit c to be a primitive form by divides c by its gcd
    c[:] = [x / d for x in c]
    k = m[0, m.ncols() - 1]
    res = [[]]
    #each loop below will add a connected component of m to res
    for i in range(1, int(d) + 1):
        #each temp represent a connected component of m
        temp = []
        for j in c:
            temp.append(j)
        #each cons calculate one of the degree d root of 1 in complex plane
        #which should be the constant terms in each connected components of m
        cons = i / d + k / d
        #since the constant is periodic, that is S^1 is issomorphic to R\Z
        #we can restric the range for cons to be (0,1]
        while cons > 1: cons = cons - 1
        while cons <= 0: cons = cons + 1
        temp.append(cons)
        res.append(temp)
    res.pop(0)
    #if want res to be matrix, flatten it
    return res

#Other helper functions for matrix
def charact_part(m):
    '''
        for m being a toric arrangement in matrix form
        remove the last colum
        return the matrix of characteristics
        
        TEST:
        sage: m = matrix(QQ,2,4,[1,2,3,1,0,2,3,1])
        sage: m
        [1 2 3 1]
        [0 2 3 1]
        sage: c = charact_part(m)
        sage: c
        [1 2 3]
        [0 2 3]
        '''
    return m.delete_columns([m.ncols()-1])

def matrix_append_row(m1, m2):
    '''
        NOTE: This is a helper function for poset_of_layer function
        
        INPUT: two matrices. m1 and m2 have the same number of columns,
        but m2 is restricted to have only one row (representing a torus)
        
        OUTPUT: return a matrix that append m2 as the last row of m1,
        remaining m1, m2 unchanged
        
        TEST:
        sage: m1 = matrix(QQ,2,4,[1,2,3,1,4,5,6,1])
        sage: m2 = matrix(QQ,1,4,[7,8,9,1])
        sage: m1
        [1 2 3 1]
        [4 5 6 1]
        sage: m2
        [7 8 9 1]
        sage: m3 = matrix_append_row(m1,m2)
        sage: m3
        [1 2 3 1]
        [4 5 6 1]
        [7 8 9 1]
        sage: m1
        [1 2 3 1]
        [4 5 6 1]
        '''
    l = []
    for i in range(0, m2.ncols()):
        l.append(m2[0][i])
    return matrix(m1.rows() + [l])

def matrix_erase_rows(m, k):
    '''
        INPUT: m, a matrix; k, number of rows to remain
        
        OUTPUT: the matrix obtained by erasing rows after the kth row
        
        TEST:
        sage: m = matrix(QQ,3,3,[1,0,0,0,1,0,0,0,0])
        sage: m
        [1 0 0]
        [0 1 0]
        [0 0 0]
        sage: k = matrix_erase_rows(m, 2)
        sage: k
        [1 0 0]
        [0 1 0]
        '''
    l = []
    for i in range(k):
        for j in m[i]:
            l.append(j)
    return matrix(QQ, k, m.ncols(), l)

def matrix_append_column(m, v):
    '''
        TEST:
        sage: m = matrix(QQ,2,3,[1,2,3,4,5,6])
        sage: m
        [1 2 3]
        [4 5 6]
        sage: v = [7,8]
        sage: res = matrix_append_column(m, v)
        sage: res
        [1 2 3 7]
        [4 5 6 8]
        '''
    l = []
    for i in range(m.nrows()):
        for j in m[i]:
            l.append(j)
        l.append(v[i])
    res = matrix(QQ, m.nrows(), m.ncols() + 1, l)
    return res

def matrices_from_nested_list(L):
    '''
        INPUT: list of list of list
        
        OUTPUT: take one connected component in each torus in the arrangement,
        return the list of all possible matrices
        
        TEST:
        sage: L = [[[1,1,1],[1,1,1/2]],[[0,1,1],[0,1,1/2]]]
        sage: L
        [[[1, 1, 1], [1, 1, 1/2]], [[0, 1, 1], [0, 1, 1/2]]]
        sage: M = matrices_from_nested_list(L)
        sage: M
        [
        [1 1 1]  [  1   1   1]  [  1   1 1/2]  [  1   1 1/2]
        [0 1 1], [  0   1 1/2], [  0   1   1], [  0   1 1/2]
        ]
        '''
    if (len(L) == 1):
        lm = []
        for i in L[0]:
            lm.append(matrix(i))
        return lm
    else:
        fr = L.pop(len(L) - 1)
        lr = matrices_from_nested_list(L)
        res = []
        for m in lr:
            for r in fr:
                #r is already a list
                temp = matrix(m.rows() + [r])
                res.append(temp)
        return res

def list_to_matrix(l):
    '''
        since we will be switch from list to matrix a lot,
        I implemented it for convenience
        
        TEST:
        sage: l = [[1,2,3],[4,5,6]]
        sage: m = list_to_matrix(l)
        sage: m
        [1 2 3]
        [4 5 6]
        '''
    f = flatten(l)
    m = matrix(QQ, len(l), len(l[0]), f)
    return m


def matrix_to_list(m):
    '''
        since we will be switch from matrix to list a lot,
        I implemented it for convenience
        
        TEST:
        sage: m = matrix(QQ,2,4,[1,2,3,1,0,2,3,1])
        sage: m
        [1 2 3 1]
        [0 2 3 1]
        sage: l = matrix_to_list(m)
        sage: l
        [[1, 2, 3, 1], [0, 2, 3, 1]]
        '''
    l = [[]]
    for i in m:
        temp = []
        for j in range(0, m.ncols()):
            temp.append(i[j])
        l.append(temp)
    l.pop(0)
    return l
