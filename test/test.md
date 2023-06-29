### test_consistency
?: should we consider state variables that are not related to the property (but included in the state)

1. empty blockchain
    * two empty blockchains
    * one empty blockchain and one non-empty blockchain
    * non empty blockchain

2. Honesty
    * honest and consistent
    * honest and inconsistent
    * a dishonest and inconsistent host
    * a dishonest but consistent host

3. consistent
    * all consistent
        * honest and consistent
        * dishonest but consistent
        * some dishonest and inconsistent
    * some trace inconsistent
        * honest and inconsistent
        * dishonest exists but others inconsistent
            * dishonest consistent / inconsistent


important element: isHonest, consistent

0, 1, many

* normal
    * all empty
    * partially empty (longest is one / more)
    * only genesis
    * all same (one/more)
    * one is very long (others one/more) / one is very short (others one/more)
    * average (one/more)


* adversary
    * adversary does not cause inconsistency
    * adversary does cause inconsistency
        * by diffrent ordering
        * by repetition
        * by new block
        * by not having genesis block

* invalid
    * similar as adversary
    
* other states
    * config
    * env
    * node state
    * message




*** adv state cannot change -- does not actually affect correctness

*** can have more than one adversary

other state -- may not be considered part of spec?

should I test other smaller functions used by spec
    - compared to those, test consistency is like an end-to-end testing


the key to write a comprehensive test case is to understand the requirement fully

maybe more useful on more difficult specs



<= is equivalent to saying that no contradiction

If blockchain a <= blockchain b, then to the last sequence number of a, there is no contradiction. For the latter elements, there are no contradictions since a does not have any other elements.

If no contradiction, then blockchain a == blockchain b at all i, where i is the index defined for both blockchain. Thus, to the last element that is defined for the shorter blockchain, a[i] == b[i]. Say a is the shorter one, then a <= b.


adversial state changes, DSNext fails
more kind of messages -- proof 