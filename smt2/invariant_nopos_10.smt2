(declare-const a Int)
(declare-const a_1 Int)
(declare-const a_2 Int)
(declare-const a_3 Int)
(declare-const a_4 Int)
(declare-const a_5 Int)
(declare-const a_6 Int)
(declare-const a_7 Int)
(declare-const c Int)
(declare-const c_1 Int)
(declare-const c_2 Int)
(declare-const c_3 Int)
(declare-const dir Bool)
(declare-const dir_1 Bool)
(declare-const dir_2 Bool)
(declare-const dir_3 Bool)
(declare-const dir_4 Bool)
(declare-const dir_5 Bool)
(declare-const dir_6 Bool)
(declare-const dir_7 Bool)
(declare-const dir_8 Bool)
(declare-const dir_9 Bool)
(declare-const dir_10 Bool)
(declare-const dir_11 Bool)
(declare-const dir_12 Bool)
(declare-const dir_13 Bool)
(declare-const dir_14 Bool)
(declare-const dir_15 Bool)
(declare-const dir_16 Bool)
(declare-const dir_17 Bool)
(declare-const dir_18 Bool)
(declare-const dir_19 Bool)
(declare-const dir_20 Bool)
(declare-const dir_21 Bool)
(declare-const dir_22 Bool)
(declare-const dir_23 Bool)
(declare-const dir_24 Bool)
(declare-const dir_25 Bool)
(declare-const dir_26 Bool)
(declare-const dir_27 Bool)
(declare-const dir_28 Bool)
(declare-const dir_29 Bool)
(declare-const dir_30 Bool)
(declare-const dir_31 Bool)
(declare-const dir_32 Bool)
(declare-const dir_33 Bool)
(declare-const dir_34 Bool)
(declare-const dir_35 Bool)
(declare-const dir_36 Bool)
(declare-const dir_37 Bool)
(declare-const dir_38 Bool)
(declare-const dir_39 Bool)
(declare-const pos Int)
(declare-const pos_1 Int)
(declare-const pos_2 Int)
(declare-const pos_3 Int)
(declare-const pos_4 Int)
(declare-const pos_5 Int)
(declare-const pos_6 Int)
(declare-const pos_7 Int)
(declare-const pos_8 Int)
(declare-const pos_9 Int)
(declare-const pos_10 Int)
(declare-const pos_11 Int)
(declare-const pos_12 Int)
(declare-const pos_13 Int)
(declare-const pos_14 Int)
(declare-const pos_15 Int)
(declare-const pos_16 Int)
(declare-const pos_17 Int)
(declare-const pos_18 Int)
(declare-const pos_19 Int)
(declare-const pos_20 Int)
(declare-const pos_21 Int)
(declare-const pos_22 Int)
(declare-const pos_23 Int)
(declare-const pos_24 Int)
(declare-const pos_25 Int)
(declare-const pos_26 Int)
(declare-const pos_27 Int)
(declare-const pos_28 Int)
(declare-const pos_29 Int)
(declare-const pos_30 Int)
(declare-const pos_31 Int)
(declare-const pos_32 Int)
(declare-const pos_33 Int)
(declare-const pos_34 Int)
(declare-const pos_35 Int)
(declare-const pos_36 Int)
(declare-const pos_37 Int)
(declare-const pos_38 Int)
(declare-const pos_39 Int)
(assert (>= a 0))
(assert (>= a_1 0))
(assert (>= a_2 0))
(assert (>= a_3 0))
(assert (>= a_4 0))
(assert (>= a_5 0))
(assert (>= a_6 0))
(assert (>= a_7 0))
(assert (>= c 0))
(assert (>= c_1 0))
(assert (>= c_2 0))
(assert (>= c_3 0))
(assert (>= pos 0))
(assert (>= pos_1 0))
(assert (>= pos_2 0))
(assert (>= pos_3 0))
(assert (>= pos_4 0))
(assert (>= pos_5 0))
(assert (>= pos_6 0))
(assert (>= pos_7 0))
(assert (>= pos_8 0))
(assert (>= pos_9 0))
(assert (>= pos_10 0))
(assert (>= pos_11 0))
(assert (>= pos_12 0))
(assert (>= pos_13 0))
(assert (>= pos_14 0))
(assert (>= pos_15 0))
(assert (>= pos_16 0))
(assert (>= pos_17 0))
(assert (>= pos_18 0))
(assert (>= pos_19 0))
(assert (>= pos_20 0))
(assert (>= pos_21 0))
(assert (>= pos_22 0))
(assert (>= pos_23 0))
(assert (>= pos_24 0))
(assert (>= pos_25 0))
(assert (>= pos_26 0))
(assert (>= pos_27 0))
(assert (>= pos_28 0))
(assert (>= pos_29 0))
(assert (>= pos_30 0))
(assert (>= pos_31 0))
(assert (>= pos_32 0))
(assert (>= pos_33 0))
(assert (>= pos_34 0))
(assert (>= pos_35 0))
(assert (>= pos_36 0))
(assert (>= pos_37 0))
(assert (>= pos_38 0))
(assert (>= pos_39 0))
(assert
 (not
  (=>
   (and (<= pos 4) (<= pos_4 4) (<= pos_1 4) (<= pos_2 4) (<= pos_3 4)
    (<= pos_5 4) (<= pos_9 4) (<= pos_6 4) (<= pos_7 4) (<= pos_8 4)
    (<= pos_10 4) (<= pos_14 4) (<= pos_11 4) (<= pos_12 4) (<= pos_13 4)
    (<= pos_15 4) (<= pos_19 4) (<= pos_16 4) (<= pos_17 4) (<= pos_18 4)
    (<= pos_20 4) (<= pos_30 4) (<= pos_24 4) (<= pos_34 4) (<= pos_21 4)
    (<= pos_31 4) (<= pos_22 4) (<= pos_32 4) (<= pos_23 4) (<= pos_33 4)
    (<= pos_25 4) (<= pos_35 4) (<= pos_29 4) (<= pos_39 4) (<= pos_26 4)
    (<= pos_36 4) (<= pos_27 4) (<= pos_37 4) (<= pos_28 4) (<= pos_38 4)
    (= a_2
     (+ a (ite (= pos 1) 1 0) (ite (= pos_5 1) 1 0) (ite (= pos_2 1) 1 0)
      (ite (= pos_7 1) 1 0) (ite (= pos_1 1) 1 0) (ite (= pos_6 1) 1 0)
      (ite (= pos_3 1) 1 0) (ite (= pos_8 1) 1 0) (ite (= pos_4 1) 1 0)
      (ite (= pos_9 1) 1 0)))
    (= c_1
     (+ c (ite (= pos 3) 1 0) (ite (= pos_5 3) 1 0) (ite (= pos_2 3) 1 0)
      (ite (= pos_7 3) 1 0) (ite (= pos_1 3) 1 0) (ite (= pos_6 3) 1 0)
      (ite (= pos_3 3) 1 0) (ite (= pos_8 3) 1 0) (ite (= pos_4 3) 1 0)
      (ite (= pos_9 3) 1 0)))
    (= a_3
     (+ a_1 (ite (= pos 2) 1 0) (ite (= pos_5 2) 1 0) (ite (= pos_2 2) 1 0)
      (ite (= pos_7 2) 1 0) (ite (= pos_1 2) 1 0) (ite (= pos_6 2) 1 0)
      (ite (= pos_3 2) 1 0) (ite (= pos_8 2) 1 0) (ite (= pos_4 2) 1 0)
      (ite (= pos_9 2) 1 0)))
    (=> (= pos 1) (and (= pos_10 (ite dir 4 0)) (iff dir_10 dir)))
    (=> (= pos 2) (and (= pos_10 (ite dir 3 0)) (iff dir_10 dir)))
    (=> (= pos 3) (and (= pos_10 (ite dir 4 2)) (iff dir_10 dir)))
    (=> (= pos 0) (and (or (= pos_10 1) (= pos_10 2)) dir_10))
    (=> (and (= pos 0) (= pos_10 1)) (<= a_1 a))
    (=> (and (= pos 0) (= pos_10 2)) (<= a a_1))
    (=> (= pos 4) (and (or (= pos_10 1) (= pos_10 3)) (not dir_10)))
    (=> (and (= pos 4) (= pos_10 1)) (<= c a))
    (=> (and (= pos 4) (= pos_10 3)) (<= a c))
    (=> (= pos_4 1) (and (= pos_14 (ite dir_4 4 0)) (iff dir_14 dir_4)))
    (=> (= pos_4 2) (and (= pos_14 (ite dir_4 3 0)) (iff dir_14 dir_4)))
    (=> (= pos_4 3) (and (= pos_14 (ite dir_4 4 2)) (iff dir_14 dir_4)))
    (=> (= pos_4 0) (and (or (= pos_14 1) (= pos_14 2)) dir_14))
    (=> (and (= pos_4 0) (= pos_14 1)) (<= a_1 a))
    (=> (and (= pos_4 0) (= pos_14 2)) (<= a a_1))
    (=> (= pos_4 4) (and (or (= pos_14 1) (= pos_14 3)) (not dir_14)))
    (=> (and (= pos_4 4) (= pos_14 1)) (<= c a))
    (=> (and (= pos_4 4) (= pos_14 3)) (<= a c))
    (=> (= pos_1 1) (and (= pos_11 (ite dir_1 4 0)) (iff dir_11 dir_1)))
    (=> (= pos_1 2) (and (= pos_11 (ite dir_1 3 0)) (iff dir_11 dir_1)))
    (=> (= pos_1 3) (and (= pos_11 (ite dir_1 4 2)) (iff dir_11 dir_1)))
    (=> (= pos_1 0) (and (or (= pos_11 1) (= pos_11 2)) dir_11))
    (=> (and (= pos_1 0) (= pos_11 1)) (<= a_1 a))
    (=> (and (= pos_1 0) (= pos_11 2)) (<= a a_1))
    (=> (= pos_1 4) (and (or (= pos_11 1) (= pos_11 3)) (not dir_11)))
    (=> (and (= pos_1 4) (= pos_11 1)) (<= c a))
    (=> (and (= pos_1 4) (= pos_11 3)) (<= a c))
    (=> (= pos_2 1) (and (= pos_12 (ite dir_2 4 0)) (iff dir_12 dir_2)))
    (=> (= pos_2 2) (and (= pos_12 (ite dir_2 3 0)) (iff dir_12 dir_2)))
    (=> (= pos_2 3) (and (= pos_12 (ite dir_2 4 2)) (iff dir_12 dir_2)))
    (=> (= pos_2 0) (and (or (= pos_12 1) (= pos_12 2)) dir_12))
    (=> (and (= pos_2 0) (= pos_12 1)) (<= a_1 a))
    (=> (and (= pos_2 0) (= pos_12 2)) (<= a a_1))
    (=> (= pos_2 4) (and (or (= pos_12 1) (= pos_12 3)) (not dir_12)))
    (=> (and (= pos_2 4) (= pos_12 1)) (<= c a))
    (=> (and (= pos_2 4) (= pos_12 3)) (<= a c))
    (=> (= pos_3 1) (and (= pos_13 (ite dir_3 4 0)) (iff dir_13 dir_3)))
    (=> (= pos_3 2) (and (= pos_13 (ite dir_3 3 0)) (iff dir_13 dir_3)))
    (=> (= pos_3 3) (and (= pos_13 (ite dir_3 4 2)) (iff dir_13 dir_3)))
    (=> (= pos_3 0) (and (or (= pos_13 1) (= pos_13 2)) dir_13))
    (=> (and (= pos_3 0) (= pos_13 1)) (<= a_1 a))
    (=> (and (= pos_3 0) (= pos_13 2)) (<= a a_1))
    (=> (= pos_3 4) (and (or (= pos_13 1) (= pos_13 3)) (not dir_13)))
    (=> (and (= pos_3 4) (= pos_13 1)) (<= c a))
    (=> (and (= pos_3 4) (= pos_13 3)) (<= a c))
    (=> (= pos_5 1) (and (= pos_15 (ite dir_5 4 0)) (iff dir_15 dir_5)))
    (=> (= pos_5 2) (and (= pos_15 (ite dir_5 3 0)) (iff dir_15 dir_5)))
    (=> (= pos_5 3) (and (= pos_15 (ite dir_5 4 2)) (iff dir_15 dir_5)))
    (=> (= pos_5 0) (and (or (= pos_15 1) (= pos_15 2)) dir_15))
    (=> (and (= pos_5 0) (= pos_15 1)) (<= a_1 a))
    (=> (and (= pos_5 0) (= pos_15 2)) (<= a a_1))
    (=> (= pos_5 4) (and (or (= pos_15 1) (= pos_15 3)) (not dir_15)))
    (=> (and (= pos_5 4) (= pos_15 1)) (<= c a))
    (=> (and (= pos_5 4) (= pos_15 3)) (<= a c))
    (=> (= pos_9 1) (and (= pos_19 (ite dir_9 4 0)) (iff dir_19 dir_9)))
    (=> (= pos_9 2) (and (= pos_19 (ite dir_9 3 0)) (iff dir_19 dir_9)))
    (=> (= pos_9 3) (and (= pos_19 (ite dir_9 4 2)) (iff dir_19 dir_9)))
    (=> (= pos_9 0) (and (or (= pos_19 1) (= pos_19 2)) dir_19))
    (=> (and (= pos_9 0) (= pos_19 1)) (<= a_1 a))
    (=> (and (= pos_9 0) (= pos_19 2)) (<= a a_1))
    (=> (= pos_9 4) (and (or (= pos_19 1) (= pos_19 3)) (not dir_19)))
    (=> (and (= pos_9 4) (= pos_19 1)) (<= c a))
    (=> (and (= pos_9 4) (= pos_19 3)) (<= a c))
    (=> (= pos_6 1) (and (= pos_16 (ite dir_6 4 0)) (iff dir_16 dir_6)))
    (=> (= pos_6 2) (and (= pos_16 (ite dir_6 3 0)) (iff dir_16 dir_6)))
    (=> (= pos_6 3) (and (= pos_16 (ite dir_6 4 2)) (iff dir_16 dir_6)))
    (=> (= pos_6 0) (and (or (= pos_16 1) (= pos_16 2)) dir_16))
    (=> (and (= pos_6 0) (= pos_16 1)) (<= a_1 a))
    (=> (and (= pos_6 0) (= pos_16 2)) (<= a a_1))
    (=> (= pos_6 4) (and (or (= pos_16 1) (= pos_16 3)) (not dir_16)))
    (=> (and (= pos_6 4) (= pos_16 1)) (<= c a))
    (=> (and (= pos_6 4) (= pos_16 3)) (<= a c))
    (=> (= pos_7 1) (and (= pos_17 (ite dir_7 4 0)) (iff dir_17 dir_7)))
    (=> (= pos_7 2) (and (= pos_17 (ite dir_7 3 0)) (iff dir_17 dir_7)))
    (=> (= pos_7 3) (and (= pos_17 (ite dir_7 4 2)) (iff dir_17 dir_7)))
    (=> (= pos_7 0) (and (or (= pos_17 1) (= pos_17 2)) dir_17))
    (=> (and (= pos_7 0) (= pos_17 1)) (<= a_1 a))
    (=> (and (= pos_7 0) (= pos_17 2)) (<= a a_1))
    (=> (= pos_7 4) (and (or (= pos_17 1) (= pos_17 3)) (not dir_17)))
    (=> (and (= pos_7 4) (= pos_17 1)) (<= c a))
    (=> (and (= pos_7 4) (= pos_17 3)) (<= a c))
    (=> (= pos_8 1) (and (= pos_18 (ite dir_8 4 0)) (iff dir_18 dir_8)))
    (=> (= pos_8 2) (and (= pos_18 (ite dir_8 3 0)) (iff dir_18 dir_8)))
    (=> (= pos_8 3) (and (= pos_18 (ite dir_8 4 2)) (iff dir_18 dir_8)))
    (=> (= pos_8 0) (and (or (= pos_18 1) (= pos_18 2)) dir_18))
    (=> (and (= pos_8 0) (= pos_18 1)) (<= a_1 a))
    (=> (and (= pos_8 0) (= pos_18 2)) (<= a a_1))
    (=> (= pos_8 4) (and (or (= pos_18 1) (= pos_18 3)) (not dir_18)))
    (=> (and (= pos_8 4) (= pos_18 1)) (<= c a))
    (=> (and (= pos_8 4) (= pos_18 3)) (<= a c))
    (= a_4
     (+ a_2 (ite (= pos_10 1) 1 0) (ite (= pos_15 1) 1 0)
      (ite (= pos_12 1) 1 0) (ite (= pos_17 1) 1 0) (ite (= pos_11 1) 1 0)
      (ite (= pos_16 1) 1 0) (ite (= pos_13 1) 1 0) (ite (= pos_18 1) 1 0)
      (ite (= pos_14 1) 1 0) (ite (= pos_19 1) 1 0)))
    (= c_2
     (+ c_1 (ite (= pos_10 3) 1 0) (ite (= pos_15 3) 1 0)
      (ite (= pos_12 3) 1 0) (ite (= pos_17 3) 1 0) (ite (= pos_11 3) 1 0)
      (ite (= pos_16 3) 1 0) (ite (= pos_13 3) 1 0) (ite (= pos_18 3) 1 0)
      (ite (= pos_14 3) 1 0) (ite (= pos_19 3) 1 0)))
    (= a_5
     (+ a_3 (ite (= pos_10 2) 1 0) (ite (= pos_15 2) 1 0)
      (ite (= pos_12 2) 1 0) (ite (= pos_17 2) 1 0) (ite (= pos_11 2) 1 0)
      (ite (= pos_16 2) 1 0) (ite (= pos_13 2) 1 0) (ite (= pos_18 2) 1 0)
      (ite (= pos_14 2) 1 0) (ite (= pos_19 2) 1 0)))
    (=> (= pos_10 1) (and (= pos_20 (ite dir_10 4 0)) (iff dir_20 dir_10)))
    (=> (= pos_10 2) (and (= pos_20 (ite dir_10 3 0)) (iff dir_20 dir_10)))
    (=> (= pos_10 3) (and (= pos_20 (ite dir_10 4 2)) (iff dir_20 dir_10)))
    (=> (= pos_10 0) (and (or (= pos_20 1) (= pos_20 2)) dir_20))
    (=> (and (= pos_10 0) (= pos_20 1)) (<= a_3 a_2))
    (=> (and (= pos_10 0) (= pos_20 2)) (<= a_2 a_3))
    (=> (= pos_10 4) (and (or (= pos_20 1) (= pos_20 3)) (not dir_20)))
    (=> (and (= pos_10 4) (= pos_20 1)) (<= c_1 a_2))
    (=> (and (= pos_10 4) (= pos_20 3)) (<= a_2 c_1))
    (=> (= pos_14 1) (and (= pos_24 (ite dir_14 4 0)) (iff dir_24 dir_14)))
    (=> (= pos_14 2) (and (= pos_24 (ite dir_14 3 0)) (iff dir_24 dir_14)))
    (=> (= pos_14 3) (and (= pos_24 (ite dir_14 4 2)) (iff dir_24 dir_14)))
    (=> (= pos_14 0) (and (or (= pos_24 1) (= pos_24 2)) dir_24))
    (=> (and (= pos_14 0) (= pos_24 1)) (<= a_3 a_2))
    (=> (and (= pos_14 0) (= pos_24 2)) (<= a_2 a_3))
    (=> (= pos_14 4) (and (or (= pos_24 1) (= pos_24 3)) (not dir_24)))
    (=> (and (= pos_14 4) (= pos_24 1)) (<= c_1 a_2))
    (=> (and (= pos_14 4) (= pos_24 3)) (<= a_2 c_1))
    (=> (= pos_11 1) (and (= pos_21 (ite dir_11 4 0)) (iff dir_21 dir_11)))
    (=> (= pos_11 2) (and (= pos_21 (ite dir_11 3 0)) (iff dir_21 dir_11)))
    (=> (= pos_11 3) (and (= pos_21 (ite dir_11 4 2)) (iff dir_21 dir_11)))
    (=> (= pos_11 0) (and (or (= pos_21 1) (= pos_21 2)) dir_21))
    (=> (and (= pos_11 0) (= pos_21 1)) (<= a_3 a_2))
    (=> (and (= pos_11 0) (= pos_21 2)) (<= a_2 a_3))
    (=> (= pos_11 4) (and (or (= pos_21 1) (= pos_21 3)) (not dir_21)))
    (=> (and (= pos_11 4) (= pos_21 1)) (<= c_1 a_2))
    (=> (and (= pos_11 4) (= pos_21 3)) (<= a_2 c_1))
    (=> (= pos_12 1) (and (= pos_22 (ite dir_12 4 0)) (iff dir_22 dir_12)))
    (=> (= pos_12 2) (and (= pos_22 (ite dir_12 3 0)) (iff dir_22 dir_12)))
    (=> (= pos_12 3) (and (= pos_22 (ite dir_12 4 2)) (iff dir_22 dir_12)))
    (=> (= pos_12 0) (and (or (= pos_22 1) (= pos_22 2)) dir_22))
    (=> (and (= pos_12 0) (= pos_22 1)) (<= a_3 a_2))
    (=> (and (= pos_12 0) (= pos_22 2)) (<= a_2 a_3))
    (=> (= pos_12 4) (and (or (= pos_22 1) (= pos_22 3)) (not dir_22)))
    (=> (and (= pos_12 4) (= pos_22 1)) (<= c_1 a_2))
    (=> (and (= pos_12 4) (= pos_22 3)) (<= a_2 c_1))
    (=> (= pos_13 1) (and (= pos_23 (ite dir_13 4 0)) (iff dir_23 dir_13)))
    (=> (= pos_13 2) (and (= pos_23 (ite dir_13 3 0)) (iff dir_23 dir_13)))
    (=> (= pos_13 3) (and (= pos_23 (ite dir_13 4 2)) (iff dir_23 dir_13)))
    (=> (= pos_13 0) (and (or (= pos_23 1) (= pos_23 2)) dir_23))
    (=> (and (= pos_13 0) (= pos_23 1)) (<= a_3 a_2))
    (=> (and (= pos_13 0) (= pos_23 2)) (<= a_2 a_3))
    (=> (= pos_13 4) (and (or (= pos_23 1) (= pos_23 3)) (not dir_23)))
    (=> (and (= pos_13 4) (= pos_23 1)) (<= c_1 a_2))
    (=> (and (= pos_13 4) (= pos_23 3)) (<= a_2 c_1))
    (=> (= pos_15 1) (and (= pos_25 (ite dir_15 4 0)) (iff dir_25 dir_15)))
    (=> (= pos_15 2) (and (= pos_25 (ite dir_15 3 0)) (iff dir_25 dir_15)))
    (=> (= pos_15 3) (and (= pos_25 (ite dir_15 4 2)) (iff dir_25 dir_15)))
    (=> (= pos_15 0) (and (or (= pos_25 1) (= pos_25 2)) dir_25))
    (=> (and (= pos_15 0) (= pos_25 1)) (<= a_3 a_2))
    (=> (and (= pos_15 0) (= pos_25 2)) (<= a_2 a_3))
    (=> (= pos_15 4) (and (or (= pos_25 1) (= pos_25 3)) (not dir_25)))
    (=> (and (= pos_15 4) (= pos_25 1)) (<= c_1 a_2))
    (=> (and (= pos_15 4) (= pos_25 3)) (<= a_2 c_1))
    (=> (= pos_19 1) (and (= pos_29 (ite dir_19 4 0)) (iff dir_29 dir_19)))
    (=> (= pos_19 2) (and (= pos_29 (ite dir_19 3 0)) (iff dir_29 dir_19)))
    (=> (= pos_19 3) (and (= pos_29 (ite dir_19 4 2)) (iff dir_29 dir_19)))
    (=> (= pos_19 0) (and (or (= pos_29 1) (= pos_29 2)) dir_29))
    (=> (and (= pos_19 0) (= pos_29 1)) (<= a_3 a_2))
    (=> (and (= pos_19 0) (= pos_29 2)) (<= a_2 a_3))
    (=> (= pos_19 4) (and (or (= pos_29 1) (= pos_29 3)) (not dir_29)))
    (=> (and (= pos_19 4) (= pos_29 1)) (<= c_1 a_2))
    (=> (and (= pos_19 4) (= pos_29 3)) (<= a_2 c_1))
    (=> (= pos_16 1) (and (= pos_26 (ite dir_16 4 0)) (iff dir_26 dir_16)))
    (=> (= pos_16 2) (and (= pos_26 (ite dir_16 3 0)) (iff dir_26 dir_16)))
    (=> (= pos_16 3) (and (= pos_26 (ite dir_16 4 2)) (iff dir_26 dir_16)))
    (=> (= pos_16 0) (and (or (= pos_26 1) (= pos_26 2)) dir_26))
    (=> (and (= pos_16 0) (= pos_26 1)) (<= a_3 a_2))
    (=> (and (= pos_16 0) (= pos_26 2)) (<= a_2 a_3))
    (=> (= pos_16 4) (and (or (= pos_26 1) (= pos_26 3)) (not dir_26)))
    (=> (and (= pos_16 4) (= pos_26 1)) (<= c_1 a_2))
    (=> (and (= pos_16 4) (= pos_26 3)) (<= a_2 c_1))
    (=> (= pos_17 1) (and (= pos_27 (ite dir_17 4 0)) (iff dir_27 dir_17)))
    (=> (= pos_17 2) (and (= pos_27 (ite dir_17 3 0)) (iff dir_27 dir_17)))
    (=> (= pos_17 3) (and (= pos_27 (ite dir_17 4 2)) (iff dir_27 dir_17)))
    (=> (= pos_17 0) (and (or (= pos_27 1) (= pos_27 2)) dir_27))
    (=> (and (= pos_17 0) (= pos_27 1)) (<= a_3 a_2))
    (=> (and (= pos_17 0) (= pos_27 2)) (<= a_2 a_3))
    (=> (= pos_17 4) (and (or (= pos_27 1) (= pos_27 3)) (not dir_27)))
    (=> (and (= pos_17 4) (= pos_27 1)) (<= c_1 a_2))
    (=> (and (= pos_17 4) (= pos_27 3)) (<= a_2 c_1))
    (=> (= pos_18 1) (and (= pos_28 (ite dir_18 4 0)) (iff dir_28 dir_18)))
    (=> (= pos_18 2) (and (= pos_28 (ite dir_18 3 0)) (iff dir_28 dir_18)))
    (=> (= pos_18 3) (and (= pos_28 (ite dir_18 4 2)) (iff dir_28 dir_18)))
    (=> (= pos_18 0) (and (or (= pos_28 1) (= pos_28 2)) dir_28))
    (=> (and (= pos_18 0) (= pos_28 1)) (<= a_3 a_2))
    (=> (and (= pos_18 0) (= pos_28 2)) (<= a_2 a_3))
    (=> (= pos_18 4) (and (or (= pos_28 1) (= pos_28 3)) (not dir_28)))
    (=> (and (= pos_18 4) (= pos_28 1)) (<= c_1 a_2))
    (=> (and (= pos_18 4) (= pos_28 3)) (<= a_2 c_1))
    (= a_6
     (+ a_4 (ite (= pos_20 1) 1 0) (ite (= pos_25 1) 1 0)
      (ite (= pos_22 1) 1 0) (ite (= pos_27 1) 1 0) (ite (= pos_21 1) 1 0)
      (ite (= pos_26 1) 1 0) (ite (= pos_23 1) 1 0) (ite (= pos_28 1) 1 0)
      (ite (= pos_24 1) 1 0) (ite (= pos_29 1) 1 0)))
    (= c_3
     (+ c_2 (ite (= pos_20 3) 1 0) (ite (= pos_25 3) 1 0)
      (ite (= pos_22 3) 1 0) (ite (= pos_27 3) 1 0) (ite (= pos_21 3) 1 0)
      (ite (= pos_26 3) 1 0) (ite (= pos_23 3) 1 0) (ite (= pos_28 3) 1 0)
      (ite (= pos_24 3) 1 0) (ite (= pos_29 3) 1 0)))
    (= a_7
     (+ a_5 (ite (= pos_20 2) 1 0) (ite (= pos_25 2) 1 0)
      (ite (= pos_22 2) 1 0) (ite (= pos_27 2) 1 0) (ite (= pos_21 2) 1 0)
      (ite (= pos_26 2) 1 0) (ite (= pos_23 2) 1 0) (ite (= pos_28 2) 1 0)
      (ite (= pos_24 2) 1 0) (ite (= pos_29 2) 1 0)))
    (=> (= pos_20 1) (and (= pos_30 (ite dir_20 4 0)) (iff dir_30 dir_20)))
    (=> (= pos_20 2) (and (= pos_30 (ite dir_20 3 0)) (iff dir_30 dir_20)))
    (=> (= pos_20 3) (and (= pos_30 (ite dir_20 4 2)) (iff dir_30 dir_20)))
    (=> (= pos_20 0) (and (or (= pos_30 1) (= pos_30 2)) dir_30))
    (=> (and (= pos_20 0) (= pos_30 1)) (<= a_5 a_4))
    (=> (and (= pos_20 0) (= pos_30 2)) (<= a_4 a_5))
    (=> (= pos_20 4) (and (or (= pos_30 1) (= pos_30 3)) (not dir_30)))
    (=> (and (= pos_20 4) (= pos_30 1)) (<= c_2 a_4))
    (=> (and (= pos_20 4) (= pos_30 3)) (<= a_4 c_2))
    (=> (= pos_24 1) (and (= pos_34 (ite dir_24 4 0)) (iff dir_34 dir_24)))
    (=> (= pos_24 2) (and (= pos_34 (ite dir_24 3 0)) (iff dir_34 dir_24)))
    (=> (= pos_24 3) (and (= pos_34 (ite dir_24 4 2)) (iff dir_34 dir_24)))
    (=> (= pos_24 0) (and (or (= pos_34 1) (= pos_34 2)) dir_34))
    (=> (and (= pos_24 0) (= pos_34 1)) (<= a_5 a_4))
    (=> (and (= pos_24 0) (= pos_34 2)) (<= a_4 a_5))
    (=> (= pos_24 4) (and (or (= pos_34 1) (= pos_34 3)) (not dir_34)))
    (=> (and (= pos_24 4) (= pos_34 1)) (<= c_2 a_4))
    (=> (and (= pos_24 4) (= pos_34 3)) (<= a_4 c_2))
    (=> (= pos_21 1) (and (= pos_31 (ite dir_21 4 0)) (iff dir_31 dir_21)))
    (=> (= pos_21 2) (and (= pos_31 (ite dir_21 3 0)) (iff dir_31 dir_21)))
    (=> (= pos_21 3) (and (= pos_31 (ite dir_21 4 2)) (iff dir_31 dir_21)))
    (=> (= pos_21 0) (and (or (= pos_31 1) (= pos_31 2)) dir_31))
    (=> (and (= pos_21 0) (= pos_31 1)) (<= a_5 a_4))
    (=> (and (= pos_21 0) (= pos_31 2)) (<= a_4 a_5))
    (=> (= pos_21 4) (and (or (= pos_31 1) (= pos_31 3)) (not dir_31)))
    (=> (and (= pos_21 4) (= pos_31 1)) (<= c_2 a_4))
    (=> (and (= pos_21 4) (= pos_31 3)) (<= a_4 c_2))
    (=> (= pos_22 1) (and (= pos_32 (ite dir_22 4 0)) (iff dir_32 dir_22)))
    (=> (= pos_22 2) (and (= pos_32 (ite dir_22 3 0)) (iff dir_32 dir_22)))
    (=> (= pos_22 3) (and (= pos_32 (ite dir_22 4 2)) (iff dir_32 dir_22)))
    (=> (= pos_22 0) (and (or (= pos_32 1) (= pos_32 2)) dir_32))
    (=> (and (= pos_22 0) (= pos_32 1)) (<= a_5 a_4))
    (=> (and (= pos_22 0) (= pos_32 2)) (<= a_4 a_5))
    (=> (= pos_22 4) (and (or (= pos_32 1) (= pos_32 3)) (not dir_32)))
    (=> (and (= pos_22 4) (= pos_32 1)) (<= c_2 a_4))
    (=> (and (= pos_22 4) (= pos_32 3)) (<= a_4 c_2))
    (=> (= pos_23 1) (and (= pos_33 (ite dir_23 4 0)) (iff dir_33 dir_23)))
    (=> (= pos_23 2) (and (= pos_33 (ite dir_23 3 0)) (iff dir_33 dir_23)))
    (=> (= pos_23 3) (and (= pos_33 (ite dir_23 4 2)) (iff dir_33 dir_23)))
    (=> (= pos_23 0) (and (or (= pos_33 1) (= pos_33 2)) dir_33))
    (=> (and (= pos_23 0) (= pos_33 1)) (<= a_5 a_4))
    (=> (and (= pos_23 0) (= pos_33 2)) (<= a_4 a_5))
    (=> (= pos_23 4) (and (or (= pos_33 1) (= pos_33 3)) (not dir_33)))
    (=> (and (= pos_23 4) (= pos_33 1)) (<= c_2 a_4))
    (=> (and (= pos_23 4) (= pos_33 3)) (<= a_4 c_2))
    (=> (= pos_25 1) (and (= pos_35 (ite dir_25 4 0)) (iff dir_35 dir_25)))
    (=> (= pos_25 2) (and (= pos_35 (ite dir_25 3 0)) (iff dir_35 dir_25)))
    (=> (= pos_25 3) (and (= pos_35 (ite dir_25 4 2)) (iff dir_35 dir_25)))
    (=> (= pos_25 0) (and (or (= pos_35 1) (= pos_35 2)) dir_35))
    (=> (and (= pos_25 0) (= pos_35 1)) (<= a_5 a_4))
    (=> (and (= pos_25 0) (= pos_35 2)) (<= a_4 a_5))
    (=> (= pos_25 4) (and (or (= pos_35 1) (= pos_35 3)) (not dir_35)))
    (=> (and (= pos_25 4) (= pos_35 1)) (<= c_2 a_4))
    (=> (and (= pos_25 4) (= pos_35 3)) (<= a_4 c_2))
    (=> (= pos_29 1) (and (= pos_39 (ite dir_29 4 0)) (iff dir_39 dir_29)))
    (=> (= pos_29 2) (and (= pos_39 (ite dir_29 3 0)) (iff dir_39 dir_29)))
    (=> (= pos_29 3) (and (= pos_39 (ite dir_29 4 2)) (iff dir_39 dir_29)))
    (=> (= pos_29 0) (and (or (= pos_39 1) (= pos_39 2)) dir_39))
    (=> (and (= pos_29 0) (= pos_39 1)) (<= a_5 a_4))
    (=> (and (= pos_29 0) (= pos_39 2)) (<= a_4 a_5))
    (=> (= pos_29 4) (and (or (= pos_39 1) (= pos_39 3)) (not dir_39)))
    (=> (and (= pos_29 4) (= pos_39 1)) (<= c_2 a_4))
    (=> (and (= pos_29 4) (= pos_39 3)) (<= a_4 c_2))
    (=> (= pos_26 1) (and (= pos_36 (ite dir_26 4 0)) (iff dir_36 dir_26)))
    (=> (= pos_26 2) (and (= pos_36 (ite dir_26 3 0)) (iff dir_36 dir_26)))
    (=> (= pos_26 3) (and (= pos_36 (ite dir_26 4 2)) (iff dir_36 dir_26)))
    (=> (= pos_26 0) (and (or (= pos_36 1) (= pos_36 2)) dir_36))
    (=> (and (= pos_26 0) (= pos_36 1)) (<= a_5 a_4))
    (=> (and (= pos_26 0) (= pos_36 2)) (<= a_4 a_5))
    (=> (= pos_26 4) (and (or (= pos_36 1) (= pos_36 3)) (not dir_36)))
    (=> (and (= pos_26 4) (= pos_36 1)) (<= c_2 a_4))
    (=> (and (= pos_26 4) (= pos_36 3)) (<= a_4 c_2))
    (=> (= pos_27 1) (and (= pos_37 (ite dir_27 4 0)) (iff dir_37 dir_27)))
    (=> (= pos_27 2) (and (= pos_37 (ite dir_27 3 0)) (iff dir_37 dir_27)))
    (=> (= pos_27 3) (and (= pos_37 (ite dir_27 4 2)) (iff dir_37 dir_27)))
    (=> (= pos_27 0) (and (or (= pos_37 1) (= pos_37 2)) dir_37))
    (=> (and (= pos_27 0) (= pos_37 1)) (<= a_5 a_4))
    (=> (and (= pos_27 0) (= pos_37 2)) (<= a_4 a_5))
    (=> (= pos_27 4) (and (or (= pos_37 1) (= pos_37 3)) (not dir_37)))
    (=> (and (= pos_27 4) (= pos_37 1)) (<= c_2 a_4))
    (=> (and (= pos_27 4) (= pos_37 3)) (<= a_4 c_2))
    (=> (= pos_28 1) (and (= pos_38 (ite dir_28 4 0)) (iff dir_38 dir_28)))
    (=> (= pos_28 2) (and (= pos_38 (ite dir_28 3 0)) (iff dir_38 dir_28)))
    (=> (= pos_28 3) (and (= pos_38 (ite dir_28 4 2)) (iff dir_38 dir_28)))
    (=> (= pos_28 0) (and (or (= pos_38 1) (= pos_38 2)) dir_38))
    (=> (and (= pos_28 0) (= pos_38 1)) (<= a_5 a_4))
    (=> (and (= pos_28 0) (= pos_38 2)) (<= a_4 a_5))
    (=> (= pos_28 4) (and (or (= pos_38 1) (= pos_38 3)) (not dir_38)))
    (=> (and (= pos_28 4) (= pos_38 1)) (<= c_2 a_4))
    (=> (and (= pos_28 4) (= pos_38 3)) (<= a_4 c_2))
    (> a (ite (<= a_1 c) c a_1)) (> a_2 (ite (<= a_3 c_1) c_1 a_3))
    (> a_4 (ite (<= a_5 c_2) c_2 a_5)))
   (> a_6 (ite (<= a_7 c_3) c_3 a_7)))))
(check-sat)
