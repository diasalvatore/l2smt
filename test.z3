(set-option :produce-unsat-cores true)

; sort
(define-sort Atom () Int)


; atoms
(declare-const AD.quickSort.status Atom)
(declare-const AD.quickSort.outputOrdered Atom)
(declare-const searcher Atom)
(declare-const AD.quickSort.avgSpeed Atom)
(declare-const sorter Atom)
(declare-const AD.mergeSort.status Atom)
(declare-const verified Atom)
(declare-const maxSize Atom)
(declare-const binarySearch Atom)
(declare-const quickSort Atom)
(declare-const mergeSort Atom)
(declare-const AD.mergeSort.outputOrdered Atom)
(declare-const AD.mergeSort.avgSpeed Atom)
(declare-const avgSpeed Atom)
(declare-const outputOrdered Atom)
(declare-const AD.binarySearch.status Atom)
(declare-const status Atom)
(declare-const string5 Atom) ; avgSpeed
(declare-const string8 Atom) ; binarySearch
(declare-const string7 Atom) ; maxSize
(declare-const string10 Atom) ; mergeSort
(declare-const string3 Atom) ; outputOrdered
(declare-const string9 Atom) ; quickSort
(declare-const string4 Atom) ; searcher
(declare-const string6 Atom) ; sorter
(declare-const string1 Atom) ; status
(declare-const string0 Atom) ; true
(declare-const string2 Atom) ; verified

; predicates
(declare-fun valueOf (Atom) Int)
(declare-fun nameOf (Atom) Int)
(define-fun isReal ((p0 Atom) ) Bool false)
(define-fun isAttrDS ((p0 Atom) ) Bool  (if (or 
   (= p0 AD.quickSort.outputOrdered)
   (= p0 AD.mergeSort.avgSpeed)
   (= p0 AD.quickSort.avgSpeed)
   (= p0 AD.mergeSort.status)
   (= p0 AD.binarySearch.status)
   (= p0 AD.mergeSort.outputOrdered)
   (= p0 AD.quickSort.status)
  ) true false))
(define-fun isRole ((p0 Atom) ) Bool  (if (or 
   (= p0 searcher)
   (= p0 sorter)
  ) true false))
(define-fun isDS ((p0 Atom) ) Bool  (if (or 
   (= p0 binarySearch)
   (= p0 quickSort)
   (= p0 mergeSort)
  ) true false))
(define-fun hasAttr ((p0 Atom) (p1 Atom) ) Bool  (if (or 
   (and (= p0 mergeSort) (= p1 AD.mergeSort.avgSpeed))
   (and (= p0 quickSort) (= p1 AD.quickSort.status))
   (and (= p0 mergeSort) (= p1 AD.mergeSort.outputOrdered))
   (and (= p0 binarySearch) (= p1 AD.binarySearch.status))
   (and (= p0 quickSort) (= p1 AD.quickSort.avgSpeed))
   (and (= p0 quickSort) (= p1 AD.quickSort.outputOrdered))
   (and (= p0 mergeSort) (= p1 AD.mergeSort.status))
  ) true false))
(define-fun bond ((p0 Atom) (p1 Atom) (p2 Atom) ) Bool  (if (or 
   (and (= p0 binarySearch) (= p1 mergeSort) (= p2 sorter))
   (and (= p0 binarySearch) (= p1 quickSort) (= p2 sorter))
  ) true false))
(define-fun isBool ((p0 Atom) ) Bool  (if (or 
   (= p0 outputOrdered)
  ) true false))
(define-fun provides ((p0 Atom) (p1 Atom) ) Bool  (if (or 
   (and (= p0 quickSort) (= p1 sorter))
   (and (= p0 binarySearch) (= p1 searcher))
   (and (= p0 mergeSort) (= p1 sorter))
  ) true false))
(define-fun isInt ((p0 Atom) ) Bool  (if (or 
   (= p0 maxSize)
   (= p0 avgSpeed)
  ) true false))
(define-fun isString ((p0 Atom) ) Bool  (if (or 
   (= p0 status)
  ) true false))
(define-fun hasRole ((p0 Atom) (p1 Atom) ) Bool false)
(define-fun uses ((p0 Atom) (p1 Atom) ) Bool  (if (or 
   (and (= p0 binarySearch) (= p1 mergeSort))
   (and (= p0 binarySearch) (= p1 quickSort))
  ) true false))
(define-fun isAttrE ((p0 Atom) ) Bool false)
(define-fun consumes ((p0 Atom) (p1 Atom) ) Bool  (if (or 
   (and (= p0 binarySearch) (= p1 sorter))
  ) true false))

; atoms unique val 
(assert (= AD.quickSort.status 0))
(assert (= AD.quickSort.outputOrdered 1))
(assert (= searcher 2))
(assert (= AD.quickSort.avgSpeed 3))
(assert (= sorter 4))
(assert (= AD.mergeSort.status 5))
(assert (= verified 6))
(assert (= maxSize 7))
(assert (= binarySearch 8))
(assert (= quickSort 9))
(assert (= mergeSort 10))
(assert (= AD.mergeSort.outputOrdered 11))
(assert (= AD.mergeSort.avgSpeed 12))
(assert (= avgSpeed 13))
(assert (= outputOrdered 14))
(assert (= AD.binarySearch.status 15))
(assert (= status 16))
(assert (! (and (= string5 17) (= (valueOf string5) 17) ) :named StringPool_17))
(assert (! (and (= string8 18) (= (valueOf string8) 18) ) :named StringPool_18))
(assert (! (and (= string7 19) (= (valueOf string7) 19) ) :named StringPool_19))
(assert (! (and (= string10 20) (= (valueOf string10) 20) ) :named StringPool_20))
(assert (! (and (= string3 21) (= (valueOf string3) 21) ) :named StringPool_21))
(assert (! (and (= string9 22) (= (valueOf string9) 22) ) :named StringPool_22))
(assert (! (and (= string4 23) (= (valueOf string4) 23) ) :named StringPool_23))
(assert (! (and (= string6 24) (= (valueOf string6) 24) ) :named StringPool_24))
(assert (! (and (= string1 25) (= (valueOf string1) 25) ) :named StringPool_25))
(assert (! (and (= string0 26) (= (valueOf string0) 26) ) :named StringPool_26))
(assert (! (and (= string2 27) (= (valueOf string2) 27) ) :named StringPool_27))

; atoms names
(assert (= (nameOf AD.quickSort.status) string1))
(assert (= (nameOf AD.quickSort.outputOrdered) string3))
(assert (= (nameOf searcher) string4))
(assert (= (nameOf AD.quickSort.avgSpeed) string5))
(assert (= (nameOf sorter) string6))
(assert (= (nameOf AD.mergeSort.status) string1))
(assert (= (nameOf verified) string2))
(assert (= (nameOf maxSize) string7))
(assert (= (nameOf binarySearch) string8))
(assert (= (nameOf quickSort) string9))
(assert (= (nameOf mergeSort) string10))
(assert (= (nameOf AD.mergeSort.outputOrdered) string3))
(assert (= (nameOf AD.mergeSort.avgSpeed) string5))
(assert (= (nameOf avgSpeed) string5))
(assert (= (nameOf outputOrdered) string3))
(assert (= (nameOf AD.binarySearch.status) string1))
(assert (= (nameOf status) string1))

; parameters


(define-fun pre ((owner Atom) (client Atom) (role Atom)) Bool 
  (if 
  (and (= owner quickSort) (= role sorter))
    (if (< (valueOf maxSize )  500) true false) (if 
  (and (= owner binarySearch) (= role sorter))
    (if (exists ((a0 Atom) (a1 Atom) ) (and  (isAttrDS a0)  (hasAttr client a0) (= (nameOf a0) string5) (isAttrDS a1)  (hasAttr client a1) (= (nameOf a1) string3) (and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) ))(and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) )))) true false) (if 
  (and (= owner mergeSort) (= role sorter))
    (if (< (valueOf maxSize )  500) true false) (if true true true)))) 
)

(define-fun post ((owner Atom) (client Atom) (role Atom)) Bool 
  (if true true true) 
)
; ---== Properties ==---

; the following predicates are mutually exclusive
(assert (! (forall ((x Atom)) (=> (= (isBool x) true) (and (= (isInt x) false) (= (isReal x) false) (= (isString x) false) (= (isRole x) false) (= (isDS x) false)))) :named multipleType_Bool))
(assert (! (forall ((x Atom)) (=> (= (isInt x) true) (and (= (isBool x) false) (= (isReal x) false) (= (isString x) false) (= (isRole x) false) (= (isDS x) false)))) :named multipleType_Int))
(assert (! (forall ((x Atom)) (=> (= (isReal x) true) (and (= (isBool x) false) (= (isInt x) false) (= (isString x) false) (= (isRole x) false) (= (isDS x) false)))) :named multipleType_Real))
(assert (! (forall ((x Atom)) (=> (= (isString x) true) (and (= (isBool x) false) (= (isInt x) false) (= (isReal x) false) (= (isRole x) false) (= (isDS x) false)))) :named multipleType_String))
(assert (! (forall ((x Atom)) (=> (= (isRole x) true) (and (= (isBool x) false) (= (isInt x) false) (= (isReal x) false) (= (isString x) false) (= (isDS x) false)))) :named multipleType_Role))
(assert (! (forall ((x Atom)) (=> (= (isDS x) true) (and (= (isBool x) false) (= (isInt x) false) (= (isReal x) false) (= (isString x) false) (= (isRole x) false)))) :named multipleType_DS))


; ---=== User Defined Assertions ===--- 
; [[Preamble]]
(assert (! (= (isInt maxSize) true) :named idPreamble_0))
(assert (! (= (isDS quickSort) true) :named idPreamble_1))
(assert (! (= (provides quickSort sorter) true) :named idPreamble_2))
(assert (! (= (isAttrDS AD.quickSort.status) true) :named idPreamble_3))
(assert (! (= (hasAttr quickSort AD.quickSort.status) true) :named idPreamble_4))
(assert (! (= (valueOf AD.quickSort.status )   (valueOf verified ) ) :named idPreamble_5))
(assert (! (= (isAttrDS AD.quickSort.avgSpeed) true) :named idPreamble_6))
(assert (! (= (hasAttr quickSort AD.quickSort.avgSpeed) true) :named idPreamble_7))
(assert (! (= (valueOf AD.quickSort.avgSpeed )  100) :named idPreamble_8))
(assert (! (= (isAttrDS AD.quickSort.outputOrdered) true) :named idPreamble_9))
(assert (! (= (hasAttr quickSort AD.quickSort.outputOrdered) true) :named idPreamble_10))
(assert (! (= (valueOf AD.quickSort.outputOrdered )   (valueOf string0 ) ) :named idPreamble_11))
(assert (! (= (isRole sorter) true) :named idPreamble_12))
(assert (! (= (isString status) true) :named idPreamble_13))
(assert (! (= (isInt avgSpeed) true) :named idPreamble_14))
(assert (! (= (isBool outputOrdered) true) :named idPreamble_15))
(assert (! (= (isDS mergeSort) true) :named idPreamble_16))
(assert (! (= (provides mergeSort sorter) true) :named idPreamble_17))
(assert (! (= (isAttrDS AD.mergeSort.status) true) :named idPreamble_18))
(assert (! (= (hasAttr mergeSort AD.mergeSort.status) true) :named idPreamble_19))
(assert (! (= (valueOf AD.mergeSort.status )   (valueOf verified ) ) :named idPreamble_20))
(assert (! (= (isAttrDS AD.mergeSort.avgSpeed) true) :named idPreamble_21))
(assert (! (= (hasAttr mergeSort AD.mergeSort.avgSpeed) true) :named idPreamble_22))
(assert (! (= (valueOf AD.mergeSort.avgSpeed )  50) :named idPreamble_23))
(assert (! (= (isAttrDS AD.mergeSort.outputOrdered) true) :named idPreamble_24))
(assert (! (= (hasAttr mergeSort AD.mergeSort.outputOrdered) true) :named idPreamble_25))
(assert (! (= (valueOf AD.mergeSort.outputOrdered )   (valueOf string0 ) ) :named idPreamble_26))
(assert (! (= (isRole sorter) true) :named idPreamble_27))
(assert (! (= (isString status) true) :named idPreamble_28))
(assert (! (= (isInt avgSpeed) true) :named idPreamble_29))
(assert (! (= (isBool outputOrdered) true) :named idPreamble_30))
(assert (! (= (isDS binarySearch) true) :named idPreamble_31))
(assert (! (= (consumes binarySearch sorter) true) :named idPreamble_32))
(assert (! (= (provides binarySearch searcher) true) :named idPreamble_33))
(assert (! (= (isAttrDS AD.binarySearch.status) true) :named idPreamble_34))
(assert (! (= (hasAttr binarySearch AD.binarySearch.status) true) :named idPreamble_35))
(assert (! (= (valueOf AD.binarySearch.status )   (valueOf verified ) ) :named idPreamble_36))
(assert (! (= (isRole sorter) true) :named idPreamble_37))
(assert (! (= (isRole searcher) true) :named idPreamble_38))
(assert (! (= (isString status) true) :named idPreamble_39))
(assert (! (= (valueOf maxSize )  600) :named idPreamble_40))
(assert (! (= (isDS binarySearch) true) :named idPreamble_41))
(assert (! (= (isDS quickSort) true) :named idPreamble_42))
(assert (! (= (isRole sorter) true) :named idPreamble_43))
(assert (! (= (consumes binarySearch sorter) true) :named idPreamble_44))
(assert (! (= (provides quickSort sorter) true) :named idPreamble_45))
(assert (! (and (= (pre binarySearch quickSort sorter) true) (= (pre quickSort binarySearch sorter) true)) :named idPreamble_46))
(assert (! (= (isDS binarySearch) true) :named idPreamble_47))
(assert (! (= (isDS mergeSort) true) :named idPreamble_48))
(assert (! (= (isRole sorter) true) :named idPreamble_49))
(assert (! (= (consumes binarySearch sorter) true) :named idPreamble_50))
(assert (! (= (provides mergeSort sorter) true) :named idPreamble_51))
(assert (! (and (= (pre binarySearch mergeSort sorter) true) (= (pre mergeSort binarySearch sorter) true)) :named idPreamble_52))
(assert (! (forall ((ds1 Atom) (ds2 Atom) (a Atom) ) (=> (and (= (isAttrDS a) true) (= (isDS ds2) true) (= (isDS ds1) true) ) (=> (and (and (= (isString a) true) (= (nameOf a) string1)) (= (uses ds1 ds2) true)) (= (valueOf a )   (valueOf string2 ) )))) :named idPreamble_53))


(check-sat)
(get-unsat-core)
