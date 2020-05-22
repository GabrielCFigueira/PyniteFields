#!/usr/bin/python                                                                  
# -*- coding: utf-8 -*-                                                            
#                                                                                  
# fieldelement.py: A class for elements in a finite field. 
#                                                                                  
# © 2016 Olivia Di Matteo (odimatte@uwaterloo.ca)                                  
#                                                                                  
# This file is part of the project PyniteFields.                                      
# Licensed under BSD-3-Clause                                                      
# 

import math
import numpy

from pynitefields.pthrootofunity import pthRootOfUnity


def xgcd(a, b):
    """return (g, x, y) such that a*x + b*y = g = gcd(a, b)"""
    x0, x1, y0, y1 = 0, 1, 1, 0
    while a != 0:
        #print("a: " + str(a) + " b: " + str(b))
        q, a, b = b // a, b % a, a
        y0, y1 = y1, y0 - q * y1
        x0, x1 = x1, x0 - q * x1
    return b, x0, y0

def inverse(number, mod):
    g, x, _ = xgcd(number, mod)
    if g != 1:
        raise ValueError(str(g) + "Isnt mod a prime?")
    return x

def polyxgcd(a, b, irre, mod):
    """return (g, x, y) such that a*x + b*y = g = gcd(a, b)"""
    
    if degree(a) == 0:
        b, x0, y0 = xgcd(a[0], mod)
        b = [b % mod] + [0] * (degree(irre) - 1)
        x0 = [x0 % mod] + [0] * (degree(irre) - 1)
        y0 = [y0 % mod] + [0] * (degree(irre) - 1)
    elif degree(b) == 0:
        b, x0, y0 = xgcd(b[0], mod)
        b = [b % mod] + [0] * (degree(irre) - 1)
        x0 = [x0 % mod] + [0] * (degree(irre) - 1)
        y0 = [y0 % mod] + [0] * (degree(irre) - 1)
    else:
        order = max(len(a), len(b))
        x0, x1, y0, y1 = [0] * order, [1] + [0] * (order - 1), [1] + [0] * (order - 1), [0] * order
        while a != [0] * len(a):
            q, r = polydiv(b, a, mod)
            a, b = r, a
            y0, y1 = y1, polysub(y0, polymul(q, y1, irre, mod), mod)
            x0, x1 = x1, polysub(x0, polymul(q, x1, irre, mod), mod)
    rest = b[0]
    if rest != 1:
        for i in range(len(b)):
            b[i] = b[i] * inverse(rest, mod) % mod
            x0[i] = x0[i] * inverse(rest, mod) % mod
            y0[i] = y0[i] * inverse(rest, mod) % mod
    return b, x0, y0

def polyinverse(a, irre, mod):
    g, x, _ = polyxgcd(a, irre, irre, mod)
    if g != [1] + [0] * (len(g) - 1):
        raise ValueError(str(g) + " Isnt mod a prime? " + str(x))
    return x[:degree(irre)]

def polymul(a, b, irre, mod):
    new_exp_coefs = [0] * (len(a) + len(b) + 1)
    for e in range(len(a)):
        for i in range(len(b)):
            new_exp_coefs[e + i] = (new_exp_coefs[e + i] + a[e] * b[i]) % mod 
    _ , r = polydiv(new_exp_coefs, irre, mod)
    return r[:degree(irre)]

def polysub(a, b, mod):
    order = max(len(a), len(b))
    res = []
    for i in range(order):
        if len(a) <= i:
            res += [b[i] % mod]
        elif len(b) <= i:
            res += [a[i] % mod]
        else:
            res += [(a[i] - b[i]) % mod]
    return res

def degree(poly):
    res = 0
    for e in range(len(poly)):
        if poly[e] != 0:
            res = e
    return res

def polydiv(poly, div, mod):
    quotient = [0] * len(poly)
    while degree(poly) >= degree(div) and poly != [0] * len(poly):
        temp = [0] * (degree(poly) - degree(div)) + div
        new_poly = []
        inv = inverse(temp[degree(poly)], mod)
        quotient[degree(poly) - degree(div)] = (quotient[degree(poly) - degree(div)] + inv * poly[degree(poly)]) % mod
        for e in range(len(temp)):
            temp[e] = temp[e] * inv * poly[degree(poly)] % mod
        poly = polysub(poly, temp, mod)
    return quotient, poly


class FieldElement():
    """ Class for an element in a finite field.

        Args:
            p (int): The prime order of the field this element is in.
            n (int): The degree of the field extension for the field this 
                     element is in.
            exp_coefs (list): The set of expansion coefficients of this element
                              in terms of some basis.
            field_list (list of FieldElements) - A copy of the list of all 
                     elements in the GaloisField this element is in. Empty when
                     the elements are initially constructed, and filled later
                     by the constructor of GaloisField. Inclusion 
                     of this parameter is not ideal, but greatly simplifies the 
                     implementation of many of the arithmetic operations 
                     (notably multiplication, inverse, exponentiation),
                     specifically for power of prime fields. With field_list, 
                     each element always knows its position, or power of the 
                     primitive element in the field. I'm not proud of it being
                     implemented this way, but this is the best I can do now.

        Attributes:
            p (int): The prime order of the field this element is in.
            n (int): The degree of the field extension for the field this 
                     element is in.
            dim (int): The dimension of the field, :math:`p^n`.
            prim_power (int): This element represented as a power of the 
                              primitive element of the field.
            exp_coefs (list): The set of expansion coefficients of this element
                              in terms of the polynomial basis.
            is_sdb (bool): Indicates whether this element is expressed in
                           the self-dual basis or not. False by default.
            sdb_coefs (list): The set of expansion coefficients in the self-
                              dual basis. Empty by default.
            str_rep (string): A representation of the exp_coefs as a string.
            field_list (list of FieldElements) - A copy of the list of all 
                     elements in the GaloisField this element is in.
    """

    def __init__(self, p, n, exp_coefs, field_list = [], is_sdb = False, sdb_field_list = [], sdb_coefs = [], irre_poly = []):
        self.p = p
        self.n = n
        self.dim = int(pow(p, n))

        # Set the expansion coefficients.
        # If we're in a prime field, the basis is 1, and
        # the coefficient is just the value
        self.exp_coefs = exp_coefs
        self.str_rep = ",".join([str(x) for x in exp_coefs])

        # These parameters initially gets set by the GaloisField constructor 
        # after ALL the field elements have been created. This is set only
        # for power of prime fields. However, when we perform operations on
        # elements such as addition, multiplication, we will need to 
        self.field_list = field_list

        if len(field_list) != 0:
            self.prim_power = self.field_list.index(self.str_rep)
        else:
            self.prim_power = -1

        # Prim power doesn't really make sense for prime, but set it here
        # so that we can make the rest of the code more general
        if self.n == 1:
            self.prim_power = exp_coefs[0]

        # These parameters will be something other than their default value
        # only if the to_sdb function is called on the GaloisField.
        self.is_sdb = is_sdb
        self.sdb_field_list = sdb_field_list
        self.sdb_coefs = sdb_coefs 

        # Reset the sdb coefficients after an operation if need be.
        if self.is_sdb:
            self.sdb_coefs = [int(x) for x in self.sdb_field_list[self.prim_power].split(',')] 

        # Used in case the field elements have not been generated
        self.irre_poly = irre_poly
      

    def __add__(self, el):
        """ Addition.

            Args:
                el (FieldElement): A FieldElement to add to this one.

            Returns:
                A FieldElement which is this element + el. For prime fields
                this is simply addition modulo :math:`p`, for power-of-prime
                fields we must add using the exp_coefs.
        """
        # Make sure we're in the same field!
        if (self.p != el.p) or (self.n != el.n):
            print("Error, cannot add elements from different fields!")
            return None

        # Prime case
        if self.n == 1:
            return FieldElement(self.p, self.n, [(self.prim_power + el.prim_power) % self.p])
        else: # Power of prime case
            # Coefficients simply add modulo p
            new_coefs = [(self.exp_coefs[i] + el.exp_coefs[i]) % self.p for i in range(0, self.n)]
            return FieldElement(self.p, self.n, new_coefs, self.field_list, self.is_sdb, self.sdb_field_list, irre_poly=self.irre_poly)


    def __radd__(self, el):
        """ Add a field element to the left of this one. 
        
            Addition in finite fields is commutative so this works just like
            the normal add. This is implemented so we can use 'sum' 
            over lists of FieldElement.
        """
        return self + el
    

    def __sub__(self, el):
        """ Addition.

            Args:
                el (FieldElement): A FieldElement to subtract from this one.

            Returns:
                A FieldElement which is this element - el. For prime fields
                this is simply subtraction modulo :math:`p`, for power-of-prime
                fields we must subtract using the exp_coefs.
        """
        # Make sure we're in the same field!
        if (self.p != el.p) or (self.n != el.n):
            print("Error, cannot subtract elements from different fields!")
            return None

        # Prime case
        if self.n == 1:
            return FieldElement(self.p, self.n, [(self.prim_power - el.prim_power) % self.p])
        else:  # Power of prime case
            # Coefficients subtract modulo p
            new_coefs = [(self.exp_coefs[i] - el.exp_coefs[i]) % self.p for i in range(0, self.n)]
            return FieldElement(self.p, self.n, new_coefs, self.field_list, self.is_sdb, self.sdb_field_list, irre_poly=self.irre_poly)


    def __mul__(self, el):
        """ Multiplication.

            Args: 
                el (int or FieldElement): An element to multiply with this one.
                      Can also pass an integer value.

            Returns:
                This element * el. For prime fields, this amounts to simple
                multiplication modulo :math:`p`. For power of primes, this is
                where the ugly field_list comes in handy. We can compute the
                new power of the primitive element by adding together this one
                and the one from el; we then use field_list to find the 
                corresponding FieldElement and return it.
        """
        # Multiplication by a constant (must be on the right!)
        if isinstance(el, int):
            return FieldElement(self.p, self.n, [(el * exp_coef) % self.p for exp_coef in self.exp_coefs] , self.field_list, self.is_sdb, self.sdb_field_list, irre_poly=self.irre_poly)

        # Multiplication by another FieldElement
        elif isinstance(el, FieldElement):
            # Make sure we're in the same field!
            if (self.p != el.p) or (self.n != el.n):
                print("Error, cannot multiply elements from different fields!")
                return None

            # Prime case
            if self.n == 1:
                return FieldElement(self.p, self.n, [(self.prim_power * el.prim_power) % self.p])
            # Power of prime case
            else:
                # I stored the whole list of field elements in each element for a reason...
                # Now we can multiply really easily
                if self.field_list != []:
                    # Multiplying by 0, nothing to see here
                    if el.prim_power == 0 or self.prim_power == 0: 
                        zeros = [0] * self.n
                        return FieldElement(self.p, self.n, zeros, self.field_list, self.is_sdb, self.sdb_field_list)
                    else:
                        new_exp = self.prim_power + el.prim_power # New exponent
                        # If the exponent calculated is outside the range of primitive element
                        # powers of the field, we need to wrap it around using the fact that
                        # the last field element is 1.
                        if new_exp > self.dim - 1: 
                            new_exp = ((new_exp - 1) % (self.dim - 1)) + 1
                        new_exp_coefs = [int(x) for x in self.field_list[new_exp].split(',')] 
                        return FieldElement(self.p, self.n, new_exp_coefs, self.field_list, self.is_sdb, self.sdb_field_list)
                else:
                    return FieldElement(self.p, self.n, polymul(self.exp_coefs, el.exp_coefs, self.irre_poly, self.p), irre_poly = self.irre_poly)

        else:
            raise TypeError("Unsupported operator")


    def __rmul__(self, el): # Implementing rmul so we can multiply on the left by integers
        """ Multiplication from the left. """
        return self * el
 

    def __truediv__(self, el):
        """ Division.

            In a Galois Field division is just multiplying by the inverse. By
            definition of a finite field, every element has a multiplicative
            inverse, except for 0.

            Args:
                An element to divide this one by.

            Returns:
                This element / el. Returns None if el = 0. 
        """
        if isinstance(el, FieldElement):
            if (self.p != el.p) or (self.n != el.n):
                print("Error, cannot divide elements from different fields.")

            # Prime
            if self.n == 1:
                if self.prim_power == 0:
                    print("Cannot divide by 0.")
                    return
            # Power of prime
            else:
                if self.field_list != [] and self.field_list.index(self.str_rep) == 0:
                    print("Cannot divide by 0.")
                    return
            # Actually do the division 
            return self * el.inv()


    # Operations with assignment
    def __iadd__(self, el):
        """ Addition with assignment. """
        return self + el


    def __isub__(self, el):
        """ Subtraction with assignment. """
        return self - el


    def __imul__(self, el):
        """ Multiplication with assignment. """
        return self * el


    def __itruediv__(self, el):
        """ Division with assignment. """
        return self / el


    def __pow__(self, exponent):
        """ Exponentiation.

            Args:
                exponent (int): Something to exponentiate this element by.

            Returns:
                This element to the power of exponent. Just the normal power
                modulo p for primes. For power-of-primes, we define that the
                power of any element to 0 is the 0 element, and *not* 1.
        """
        # Prime case
        if self.n == 1:
            return FieldElement(self.p, self.n, [int(self.prim_power ** exponent) % self.p])
        # Power of prime case
        else:
            new_coefs = []
            # 0, and any element to the 0 is 0 by convention 
            if self.field_list != []:
                if self.prim_power == 0 or exponent == 0: 
                    new_coefs = [int(x) for x in self.field_list[0].split(',')]
                else:
                    new_exp = self.prim_power * exponent
                    if new_exp > self.dim - 1:
                        new_exp = ((new_exp - 1) % (self.dim - 1)) + 1
                    new_coefs = [int(x) for x in self.field_list[new_exp].split(',')] 
                return FieldElement(self.p, self.n, new_coefs, self.field_list, self.is_sdb, self.sdb_field_list)
            else:
                poly = numpy.polynomial.polynomial.polypow(numpy.array(self.exp_coefs), exponent)
                poly = [i for i in poly]
                if len(poly) < len(self.irre_poly) - 1:
                    poly += [0] * (len(self.irre_poly) - len(poly) - 1)
                _ , r = polydiv(poly, self.irre_poly, self.p)
                return FieldElement(self.p, self.n, r[:degree(self.irre_poly)], irre_poly=self.irre_poly)

    def __eq__(self, el):
        """ Test equality of two field elements.
            
            Args:
                el (FieldElement): An element to compare with.

            Returns:
                True if the field dimensions (:math:`p`, :math:`n`) are the 
                same, the basis expansions are the same, and the list of 
                field elements is the same. False otherwise.
        """
        if (self.p != el.p) or (self.n != el.n):
            return False
        if self.exp_coefs != el.exp_coefs:
            return False
        if self.field_list != el.field_list:
            return False
        return True


    def __lt__(self, el):
        """ Implement a 'natural' ordering for field elements.

            For prime fields, this is simply the ordering of natural numbers.
            For power of primes, turn the coefficient lists into binary
            strings, and order them this way. Doing this to allow for
            Wigner functions to be plotted 'in order' in Balthasar.

            Args:
                el (FieldElement): An element to compare with.

            Returns:
                True if this element is 'less' by the conditions defined above.
                False otherwise.
        """
        if self.n == 1: 
            if self.prim_power < el.prim_power:
                return True
            else:
                return False
        else:
            # If there is a sdb defined, use that, otherwise use exp_coefs
            if self.is_sdb:
                this_exp_str = [str(x) for x in self.sdb_coefs]
                that_exp_str = [str(x) for x in el.sdb_coefs]
                if "".join(this_exp_str) < "".join(that_exp_str):
                    return True
                else:
                    return False
            else:
                this_exp_str = [str(x) for x in self.exp_coefs]
                that_exp_str = [str(x) for x in el.exp_coefs]
                if "".join(this_exp_str) < "".join(that_exp_str):
                    return True
                else:
                    return False


    def __repr__(self):
        """ Make the field element get printed in the command line."""
        if self.n == 1:
            return str(self.prim_power)
        else:
            if self.is_sdb:
                return str(self.sdb_coefs)
            else:
                return str(self.exp_coefs)


    def __hash__(self):
        """ Make hashable so we can use these guys as dictionary keys."""
        return hash(repr(self))


    def inv(self):
        """ Compute the multiplicative inverse of a field element.

            Returns:
                The FieldElement that is the inverse of this one. All
                elements have a multiplicative inverse except for 0;
                if 0 is passed, prints error message and returns None.

            Note: The trace of an element can be invoked in two ways. One can
            do el.inv() or inv(el).
        """

        if self.n == 1: # Prime case - brute force :(        not anymore
            if self.prim_power == 0:
                print("Error, 0 has no multiplicative inverse.")
                return

            return FieldElement(self.p, self.n, [inverse(self.prim_power, self.p)])
        
        else: # Power of prime case
            if self.field_list != []:
                if self.prim_power == 0:
                    print("Error, 0 has no multiplicative inverse.")
                    return 
                # Last element is always 1 which is it's own inverse
                elif self.prim_power == self.dim - 1:
                    return self 
                # All other elements, find exponent which sums to dim - 1
                else:
                    new_coefs = [int(x) for x in self.field_list[self.dim - self.prim_power - 1].split(',')]
                    return FieldElement(self.p, self.n, new_coefs, self.field_list, self.is_sdb, self.sdb_field_list)
            else:
                return FieldElement(self.p, self.n, polyinverse(self.exp_coefs, self.irre_poly, self.p), irre_poly=self.irre_poly)


    def tr(self):
        """ Compute the trace of a field element. 

            The trace of an element is defined as 

            .. math ::

              \\text{tr}(\\alpha) = \\alpha + \\alpha^p + \\alpha^{p^2} + \cdots \\alpha^{p^{n - 1}}
        
            The trace of any element should be an element of the base field 
            GF(:math:`p`) for the power of prime case.

            Returns:
                The trace of this element, as expressed above, as an integer.

            Note: The trace of an element can be invoked in two ways. One can
            do el.tr() or tr(el).
        """
        s = self

        if self.n == 1:
            return self.prim_power
        else:
            for i in range(1, self.n):
                s = s + pow(self, pow(self.p, i))

        return s.exp_coefs[0]


    def gchar(self):
        """ Compute the character of a FieldElement. 

            We define our group character as 

            .. math::

                \chi({\\alpha}) = \omega_{p}^{\\text{tr}({\\alpha})} 

            where :math:`\omega_p` is the :math:`p^\\text{th}` root of unity.

            Returns:
                :math:`\chi(\\alpha)` as defined above. For fields with 
                characteristic 2, this is an integer. For fields extended from
                odd primes, it is a pthRootOfUnity.

            Note: The trace of an element can be invoked in two ways. One can
            do el.gchar() or gchar(el).
        """
        if self.p == 2:
            return ((-1) **  self.tr())
        else:
            return pthRootOfUnity(self.p, self.tr())
            

    def print(self):
        """ Print out information about the element."""
        if self.n == 1:
            print(self.prim_power)
        else:
            if self.is_sdb:
                print(self.sdb_coefs)
            else:
                print(self.exp_coefs)
