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
(assert
 (not
  (=>
   (and (<= pos 4) (<= pos_4 4) (<= pos_1 4) (<= pos_2 4) (<= pos_3 4)
    (<= pos_5 4) (<= pos_9 4) (<= pos_6 4) (<= pos_7 4) (<= pos_8 4)
    (<= pos_10 4) (<= pos_15 4) (<= pos_14 4) (<= pos_19 4) (<= pos_11 4)
    (<= pos_16 4) (<= pos_12 4) (<= pos_17 4) (<= pos_13 4) (<= pos_18 4)
    (= a_2
     (+ a (ite (= pos 1) 1 0) (ite (= pos_2 1) 1 0) (ite (= pos_1 1) 1 0)
      (ite (= pos_3 1) 1 0) (ite (= pos_4 1) 1 0)))
    (= c_1
     (+ c (ite (= pos 3) 1 0) (ite (= pos_2 3) 1 0) (ite (= pos_1 3) 1 0)
      (ite (= pos_3 3) 1 0) (ite (= pos_4 3) 1 0)))
    (= a_3
     (+ a_1 (ite (= pos 2) 1 0) (ite (= pos_2 2) 1 0) (ite (= pos_1 2) 1 0)
      (ite (= pos_3 2) 1 0) (ite (= pos_4 2) 1 0)))
    (=> (= pos 1) (and (= pos_5 (ite dir 4 0)) (iff dir_5 dir)))
    (=> (= pos 2) (and (= pos_5 (ite dir 3 0)) (iff dir_5 dir)))
    (=> (= pos 3) (and (= pos_5 (ite dir 4 2)) (iff dir_5 dir)))
    (=> (= pos 0) (and (or (= pos_5 1) (= pos_5 2)) dir_5))
    (=> (and (= pos 0) (= pos_5 1)) (<= a_1 a))
    (=> (and (= pos 0) (= pos_5 2)) (<= a a_1))
    (=> (= pos 4) (and (or (= pos_5 1) (= pos_5 3)) (not dir_5)))
    (=> (and (= pos 4) (= pos_5 1)) (<= c a))
    (=> (and (= pos 4) (= pos_5 3)) (<= a c))
    (=> (= pos_4 1) (and (= pos_9 (ite dir_4 4 0)) (iff dir_9 dir_4)))
    (=> (= pos_4 2) (and (= pos_9 (ite dir_4 3 0)) (iff dir_9 dir_4)))
    (=> (= pos_4 3) (and (= pos_9 (ite dir_4 4 2)) (iff dir_9 dir_4)))
    (=> (= pos_4 0) (and (or (= pos_9 1) (= pos_9 2)) dir_9))
    (=> (and (= pos_4 0) (= pos_9 1)) (<= a_1 a))
    (=> (and (= pos_4 0) (= pos_9 2)) (<= a a_1))
    (=> (= pos_4 4) (and (or (= pos_9 1) (= pos_9 3)) (not dir_9)))
    (=> (and (= pos_4 4) (= pos_9 1)) (<= c a))
    (=> (and (= pos_4 4) (= pos_9 3)) (<= a c))
    (=> (= pos_1 1) (and (= pos_6 (ite dir_1 4 0)) (iff dir_6 dir_1)))
    (=> (= pos_1 2) (and (= pos_6 (ite dir_1 3 0)) (iff dir_6 dir_1)))
    (=> (= pos_1 3) (and (= pos_6 (ite dir_1 4 2)) (iff dir_6 dir_1)))
    (=> (= pos_1 0) (and (or (= pos_6 1) (= pos_6 2)) dir_6))
    (=> (and (= pos_1 0) (= pos_6 1)) (<= a_1 a))
    (=> (and (= pos_1 0) (= pos_6 2)) (<= a a_1))
    (=> (= pos_1 4) (and (or (= pos_6 1) (= pos_6 3)) (not dir_6)))
    (=> (and (= pos_1 4) (= pos_6 1)) (<= c a))
    (=> (and (= pos_1 4) (= pos_6 3)) (<= a c))
    (=> (= pos_2 1) (and (= pos_7 (ite dir_2 4 0)) (iff dir_7 dir_2)))
    (=> (= pos_2 2) (and (= pos_7 (ite dir_2 3 0)) (iff dir_7 dir_2)))
    (=> (= pos_2 3) (and (= pos_7 (ite dir_2 4 2)) (iff dir_7 dir_2)))
    (=> (= pos_2 0) (and (or (= pos_7 1) (= pos_7 2)) dir_7))
    (=> (and (= pos_2 0) (= pos_7 1)) (<= a_1 a))
    (=> (and (= pos_2 0) (= pos_7 2)) (<= a a_1))
    (=> (= pos_2 4) (and (or (= pos_7 1) (= pos_7 3)) (not dir_7)))
    (=> (and (= pos_2 4) (= pos_7 1)) (<= c a))
    (=> (and (= pos_2 4) (= pos_7 3)) (<= a c))
    (=> (= pos_3 1) (and (= pos_8 (ite dir_3 4 0)) (iff dir_8 dir_3)))
    (=> (= pos_3 2) (and (= pos_8 (ite dir_3 3 0)) (iff dir_8 dir_3)))
    (=> (= pos_3 3) (and (= pos_8 (ite dir_3 4 2)) (iff dir_8 dir_3)))
    (=> (= pos_3 0) (and (or (= pos_8 1) (= pos_8 2)) dir_8))
    (=> (and (= pos_3 0) (= pos_8 1)) (<= a_1 a))
    (=> (and (= pos_3 0) (= pos_8 2)) (<= a a_1))
    (=> (= pos_3 4) (and (or (= pos_8 1) (= pos_8 3)) (not dir_8)))
    (=> (and (= pos_3 4) (= pos_8 1)) (<= c a))
    (=> (and (= pos_3 4) (= pos_8 3)) (<= a c))
    (= a_4
     (+ a_2 (ite (= pos_5 1) 1 0) (ite (= pos_7 1) 1 0) (ite (= pos_6 1) 1 0)
      (ite (= pos_8 1) 1 0) (ite (= pos_9 1) 1 0)))
    (= c_2
     (+ c_1 (ite (= pos_5 3) 1 0) (ite (= pos_7 3) 1 0) (ite (= pos_6 3) 1 0)
      (ite (= pos_8 3) 1 0) (ite (= pos_9 3) 1 0)))
    (= a_5
     (+ a_3 (ite (= pos_5 2) 1 0) (ite (= pos_7 2) 1 0) (ite (= pos_6 2) 1 0)
      (ite (= pos_8 2) 1 0) (ite (= pos_9 2) 1 0)))
    (=> (= pos_5 1) (and (= pos_10 (ite dir_5 4 0)) (iff dir_10 dir_5)))
    (=> (= pos_5 2) (and (= pos_10 (ite dir_5 3 0)) (iff dir_10 dir_5)))
    (=> (= pos_5 3) (and (= pos_10 (ite dir_5 4 2)) (iff dir_10 dir_5)))
    (=> (= pos_5 0) (and (or (= pos_10 1) (= pos_10 2)) dir_10))
    (=> (and (= pos_5 0) (= pos_10 1)) (<= a_3 a_2))
    (=> (and (= pos_5 0) (= pos_10 2)) (<= a_2 a_3))
    (=> (= pos_5 4) (and (or (= pos_10 1) (= pos_10 3)) (not dir_10)))
    (=> (and (= pos_5 4) (= pos_10 1)) (<= c_1 a_2))
    (=> (and (= pos_5 4) (= pos_10 3)) (<= a_2 c_1))
    (=> (= pos_9 1) (and (= pos_14 (ite dir_9 4 0)) (iff dir_14 dir_9)))
    (=> (= pos_9 2) (and (= pos_14 (ite dir_9 3 0)) (iff dir_14 dir_9)))
    (=> (= pos_9 3) (and (= pos_14 (ite dir_9 4 2)) (iff dir_14 dir_9)))
    (=> (= pos_9 0) (and (or (= pos_14 1) (= pos_14 2)) dir_14))
    (=> (and (= pos_9 0) (= pos_14 1)) (<= a_3 a_2))
    (=> (and (= pos_9 0) (= pos_14 2)) (<= a_2 a_3))
    (=> (= pos_9 4) (and (or (= pos_14 1) (= pos_14 3)) (not dir_14)))
    (=> (and (= pos_9 4) (= pos_14 1)) (<= c_1 a_2))
    (=> (and (= pos_9 4) (= pos_14 3)) (<= a_2 c_1))
    (=> (= pos_6 1) (and (= pos_11 (ite dir_6 4 0)) (iff dir_11 dir_6)))
    (=> (= pos_6 2) (and (= pos_11 (ite dir_6 3 0)) (iff dir_11 dir_6)))
    (=> (= pos_6 3) (and (= pos_11 (ite dir_6 4 2)) (iff dir_11 dir_6)))
    (=> (= pos_6 0) (and (or (= pos_11 1) (= pos_11 2)) dir_11))
    (=> (and (= pos_6 0) (= pos_11 1)) (<= a_3 a_2))
    (=> (and (= pos_6 0) (= pos_11 2)) (<= a_2 a_3))
    (=> (= pos_6 4) (and (or (= pos_11 1) (= pos_11 3)) (not dir_11)))
    (=> (and (= pos_6 4) (= pos_11 1)) (<= c_1 a_2))
    (=> (and (= pos_6 4) (= pos_11 3)) (<= a_2 c_1))
    (=> (= pos_7 1) (and (= pos_12 (ite dir_7 4 0)) (iff dir_12 dir_7)))
    (=> (= pos_7 2) (and (= pos_12 (ite dir_7 3 0)) (iff dir_12 dir_7)))
    (=> (= pos_7 3) (and (= pos_12 (ite dir_7 4 2)) (iff dir_12 dir_7)))
    (=> (= pos_7 0) (and (or (= pos_12 1) (= pos_12 2)) dir_12))
    (=> (and (= pos_7 0) (= pos_12 1)) (<= a_3 a_2))
    (=> (and (= pos_7 0) (= pos_12 2)) (<= a_2 a_3))
    (=> (= pos_7 4) (and (or (= pos_12 1) (= pos_12 3)) (not dir_12)))
    (=> (and (= pos_7 4) (= pos_12 1)) (<= c_1 a_2))
    (=> (and (= pos_7 4) (= pos_12 3)) (<= a_2 c_1))
    (=> (= pos_8 1) (and (= pos_13 (ite dir_8 4 0)) (iff dir_13 dir_8)))
    (=> (= pos_8 2) (and (= pos_13 (ite dir_8 3 0)) (iff dir_13 dir_8)))
    (=> (= pos_8 3) (and (= pos_13 (ite dir_8 4 2)) (iff dir_13 dir_8)))
    (=> (= pos_8 0) (and (or (= pos_13 1) (= pos_13 2)) dir_13))
    (=> (and (= pos_8 0) (= pos_13 1)) (<= a_3 a_2))
    (=> (and (= pos_8 0) (= pos_13 2)) (<= a_2 a_3))
    (=> (= pos_8 4) (and (or (= pos_13 1) (= pos_13 3)) (not dir_13)))
    (=> (and (= pos_8 4) (= pos_13 1)) (<= c_1 a_2))
    (=> (and (= pos_8 4) (= pos_13 3)) (<= a_2 c_1))
    (= a_6
     (+ a_4 (ite (= pos_10 1) 1 0) (ite (= pos_12 1) 1 0)
      (ite (= pos_11 1) 1 0) (ite (= pos_13 1) 1 0) (ite (= pos_14 1) 1 0)))
    (= c_3
     (+ c_2 (ite (= pos_10 3) 1 0) (ite (= pos_12 3) 1 0)
      (ite (= pos_11 3) 1 0) (ite (= pos_13 3) 1 0) (ite (= pos_14 3) 1 0)))
    (= a_7
     (+ a_5 (ite (= pos_10 2) 1 0) (ite (= pos_12 2) 1 0)
      (ite (= pos_11 2) 1 0) (ite (= pos_13 2) 1 0) (ite (= pos_14 2) 1 0)))
    (=> (= pos_10 1) (and (= pos_15 (ite dir_10 4 0)) (iff dir_15 dir_10)))
    (=> (= pos_10 2) (and (= pos_15 (ite dir_10 3 0)) (iff dir_15 dir_10)))
    (=> (= pos_10 3) (and (= pos_15 (ite dir_10 4 2)) (iff dir_15 dir_10)))
    (=> (= pos_10 0) (and (or (= pos_15 1) (= pos_15 2)) dir_15))
    (=> (and (= pos_10 0) (= pos_15 1)) (<= a_5 a_4))
    (=> (and (= pos_10 0) (= pos_15 2)) (<= a_4 a_5))
    (=> (= pos_10 4) (and (or (= pos_15 1) (= pos_15 3)) (not dir_15)))
    (=> (and (= pos_10 4) (= pos_15 1)) (<= c_2 a_4))
    (=> (and (= pos_10 4) (= pos_15 3)) (<= a_4 c_2))
    (=> (= pos_14 1) (and (= pos_19 (ite dir_14 4 0)) (iff dir_19 dir_14)))
    (=> (= pos_14 2) (and (= pos_19 (ite dir_14 3 0)) (iff dir_19 dir_14)))
    (=> (= pos_14 3) (and (= pos_19 (ite dir_14 4 2)) (iff dir_19 dir_14)))
    (=> (= pos_14 0) (and (or (= pos_19 1) (= pos_19 2)) dir_19))
    (=> (and (= pos_14 0) (= pos_19 1)) (<= a_5 a_4))
    (=> (and (= pos_14 0) (= pos_19 2)) (<= a_4 a_5))
    (=> (= pos_14 4) (and (or (= pos_19 1) (= pos_19 3)) (not dir_19)))
    (=> (and (= pos_14 4) (= pos_19 1)) (<= c_2 a_4))
    (=> (and (= pos_14 4) (= pos_19 3)) (<= a_4 c_2))
    (=> (= pos_11 1) (and (= pos_16 (ite dir_11 4 0)) (iff dir_16 dir_11)))
    (=> (= pos_11 2) (and (= pos_16 (ite dir_11 3 0)) (iff dir_16 dir_11)))
    (=> (= pos_11 3) (and (= pos_16 (ite dir_11 4 2)) (iff dir_16 dir_11)))
    (=> (= pos_11 0) (and (or (= pos_16 1) (= pos_16 2)) dir_16))
    (=> (and (= pos_11 0) (= pos_16 1)) (<= a_5 a_4))
    (=> (and (= pos_11 0) (= pos_16 2)) (<= a_4 a_5))
    (=> (= pos_11 4) (and (or (= pos_16 1) (= pos_16 3)) (not dir_16)))
    (=> (and (= pos_11 4) (= pos_16 1)) (<= c_2 a_4))
    (=> (and (= pos_11 4) (= pos_16 3)) (<= a_4 c_2))
    (=> (= pos_12 1) (and (= pos_17 (ite dir_12 4 0)) (iff dir_17 dir_12)))
    (=> (= pos_12 2) (and (= pos_17 (ite dir_12 3 0)) (iff dir_17 dir_12)))
    (=> (= pos_12 3) (and (= pos_17 (ite dir_12 4 2)) (iff dir_17 dir_12)))
    (=> (= pos_12 0) (and (or (= pos_17 1) (= pos_17 2)) dir_17))
    (=> (and (= pos_12 0) (= pos_17 1)) (<= a_5 a_4))
    (=> (and (= pos_12 0) (= pos_17 2)) (<= a_4 a_5))
    (=> (= pos_12 4) (and (or (= pos_17 1) (= pos_17 3)) (not dir_17)))
    (=> (and (= pos_12 4) (= pos_17 1)) (<= c_2 a_4))
    (=> (and (= pos_12 4) (= pos_17 3)) (<= a_4 c_2))
    (=> (= pos_13 1) (and (= pos_18 (ite dir_13 4 0)) (iff dir_18 dir_13)))
    (=> (= pos_13 2) (and (= pos_18 (ite dir_13 3 0)) (iff dir_18 dir_13)))
    (=> (= pos_13 3) (and (= pos_18 (ite dir_13 4 2)) (iff dir_18 dir_13)))
    (=> (= pos_13 0) (and (or (= pos_18 1) (= pos_18 2)) dir_18))
    (=> (and (= pos_13 0) (= pos_18 1)) (<= a_5 a_4))
    (=> (and (= pos_13 0) (= pos_18 2)) (<= a_4 a_5))
    (=> (= pos_13 4) (and (or (= pos_18 1) (= pos_18 3)) (not dir_18)))
    (=> (and (= pos_13 4) (= pos_18 1)) (<= c_2 a_4))
    (=> (and (= pos_13 4) (= pos_18 3)) (<= a_4 c_2))
    (> a (ite (<= a_1 c) c a_1)) (> a_2 (ite (<= a_3 c_1) c_1 a_3))
    (> a_4 (ite (<= a_5 c_2) c_2 a_5)))
   (> a_6 (ite (<= a_7 c_3) c_3 a_7)))))
(check-sat)
