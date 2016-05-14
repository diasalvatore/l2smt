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
  (and (= owner binarySearch) (= role sorter))
    (if (exists ((a0 Atom) (a1 Atom) ) (and  (isAttrDS a0)  (hasAttr client a0) (= (nameOf a0) string5) (isAttrDS a1)  (hasAttr client a1) (= (nameOf a1) string3) (and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) ))(and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) )))) true false) (if 
  (and (= owner quickSort) (= role sorter))
    (if (<= (valueOf maxSize )  500) true false) (if 
  (and (= owner binarySearch) (= role sorter))
    (if (exists ((a0 Atom) (a1 Atom) ) (and  (isAttrDS a0)  (hasAttr client a0) (= (nameOf a0) string5) (isAttrDS a1)  (hasAttr client a1) (= (nameOf a1) string3) (and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) ))(and (< (valueOf a0 )  200) (= (valueOf a1 )   (valueOf string0 ) )))) true false) (if true true true)))) 
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
; Step 0

; [[Preamble, #925acc4d11b445ccbba02835045812abP]]
(assert (! (= (isInt maxSize) true) :named id925acc4d11b445ccbba02835045812abP_0))

; [[#a660d8f850804dbba7a5edbb6de76381P]]
(assert (! (= (isDS quickSort) true) :named ida660d8f850804dbba7a5edbb6de76381P_0))
(assert (! (= (provides quickSort sorter) true) :named ida660d8f850804dbba7a5edbb6de76381P_1))
(assert (! (= (isAttrDS AD.quickSort.status) true) :named ida660d8f850804dbba7a5edbb6de76381P_2))
(assert (! (= (hasAttr quickSort AD.quickSort.status) true) :named ida660d8f850804dbba7a5edbb6de76381P_3))
(assert (! (= (valueOf AD.quickSort.status )   (valueOf verified ) ) :named ida660d8f850804dbba7a5edbb6de76381P_4))
(assert (! (= (isAttrDS AD.quickSort.avgSpeed) true) :named ida660d8f850804dbba7a5edbb6de76381P_5))
(assert (! (= (hasAttr quickSort AD.quickSort.avgSpeed) true) :named ida660d8f850804dbba7a5edbb6de76381P_6))
(assert (! (= (valueOf AD.quickSort.avgSpeed )  100) :named ida660d8f850804dbba7a5edbb6de76381P_7))
(assert (! (= (isAttrDS AD.quickSort.outputOrdered) true) :named ida660d8f850804dbba7a5edbb6de76381P_8))
(assert (! (= (hasAttr quickSort AD.quickSort.outputOrdered) true) :named ida660d8f850804dbba7a5edbb6de76381P_9))
(assert (! (= (valueOf AD.quickSort.outputOrdered )   (valueOf string0 ) ) :named ida660d8f850804dbba7a5edbb6de76381P_10))

; [[#5e9771f3a4174a80af5842a898b69343P]]
(assert (! (= (isRole sorter) true) :named id5e9771f3a4174a80af5842a898b69343P_0))

; [[#3b0d6faf084b4d5a94c38521d170f0b7P]]
(assert (! (= (isString status) true) :named id3b0d6faf084b4d5a94c38521d170f0b7P_0))

; [[#484623c997cf450f9ddd1f2ae60740a3P]]
(assert (! (= (isInt avgSpeed) true) :named id484623c997cf450f9ddd1f2ae60740a3P_0))

; [[#81cb091a04854c43b864673610319603P]]
(assert (! (= (isBool outputOrdered) true) :named id81cb091a04854c43b864673610319603P_0))

; [[#487196ae95804376a04e2a056401be95P]]
(assert (! (= (isDS mergeSort) true) :named id487196ae95804376a04e2a056401be95P_0))
(assert (! (= (provides mergeSort sorter) true) :named id487196ae95804376a04e2a056401be95P_1))
(assert (! (= (isAttrDS AD.mergeSort.status) true) :named id487196ae95804376a04e2a056401be95P_2))
(assert (! (= (hasAttr mergeSort AD.mergeSort.status) true) :named id487196ae95804376a04e2a056401be95P_3))
(assert (! (= (valueOf AD.mergeSort.status )   (valueOf verified ) ) :named id487196ae95804376a04e2a056401be95P_4))
(assert (! (= (isAttrDS AD.mergeSort.avgSpeed) true) :named id487196ae95804376a04e2a056401be95P_5))
(assert (! (= (hasAttr mergeSort AD.mergeSort.avgSpeed) true) :named id487196ae95804376a04e2a056401be95P_6))
(assert (! (= (valueOf AD.mergeSort.avgSpeed )  201) :named id487196ae95804376a04e2a056401be95P_7))
(assert (! (= (isAttrDS AD.mergeSort.outputOrdered) true) :named id487196ae95804376a04e2a056401be95P_8))
(assert (! (= (hasAttr mergeSort AD.mergeSort.outputOrdered) true) :named id487196ae95804376a04e2a056401be95P_9))
(assert (! (= (valueOf AD.mergeSort.outputOrdered )   (valueOf string0 ) ) :named id487196ae95804376a04e2a056401be95P_10))

; [[#08dfab4f790b4facbafa09a6798a343cP]]
(assert (! (= (isRole sorter) true) :named id08dfab4f790b4facbafa09a6798a343cP_0))

; [[#9520f2ee531b430690bd34303efbceb5P]]
(assert (! (= (isString status) true) :named id9520f2ee531b430690bd34303efbceb5P_0))

; [[#3d962fe14b6140dcb245fc0034b5c905P]]
(assert (! (= (isInt avgSpeed) true) :named id3d962fe14b6140dcb245fc0034b5c905P_0))

; [[#9eceed85b84f48539c3fa45c9c8841c8P]]
(assert (! (= (isBool outputOrdered) true) :named id9eceed85b84f48539c3fa45c9c8841c8P_0))

; [[#b99e127e6ee84d72a6934921e37630a3P]]
(assert (! (= (isDS binarySearch) true) :named idb99e127e6ee84d72a6934921e37630a3P_0))
(assert (! (= (consumes binarySearch sorter) true) :named idb99e127e6ee84d72a6934921e37630a3P_1))
(assert (! (= (provides binarySearch searcher) true) :named idb99e127e6ee84d72a6934921e37630a3P_2))
(assert (! (= (isAttrDS AD.binarySearch.status) true) :named idb99e127e6ee84d72a6934921e37630a3P_3))
(assert (! (= (hasAttr binarySearch AD.binarySearch.status) true) :named idb99e127e6ee84d72a6934921e37630a3P_4))
(assert (! (= (valueOf AD.binarySearch.status )   (valueOf verified ) ) :named idb99e127e6ee84d72a6934921e37630a3P_5))

; [[#89e0ba57c9694199ad3ba34701b5a633P]]
(assert (! (= (isRole sorter) true) :named id89e0ba57c9694199ad3ba34701b5a633P_0))

; [[#be69562637a54e95b94518badd0bf745P]]
(assert (! (= (isRole searcher) true) :named idbe69562637a54e95b94518badd0bf745P_0))

; [[#73323c5ca48b48f8849d91e783aea36eP]]
(assert (! (= (isString status) true) :named id73323c5ca48b48f8849d91e783aea36eP_0))
(assert (! (= (valueOf maxSize )  500) :named id73323c5ca48b48f8849d91e783aea36eP_1))
(assert (! (forall ((ds1 Atom) (ds2 Atom) (a Atom) ) (=> (and (= (isAttrDS a) true) (= (isDS ds2) true) (= (isDS ds1) true) ) (=> (and (and (= (isString a) true) (= (nameOf a) string1)) (= (uses ds1 ds2) true)) (= (valueOf a )   (valueOf string2 ) )))) :named id73323c5ca48b48f8849d91e783aea36eP_2))

; Step 1

; [[#0f06c55a3b9f4f8a89a028018d295ae2C]]
(assert (! (= (isDS binarySearch) true) :named id0f06c55a3b9f4f8a89a028018d295ae2C_0))
(assert (! (= (isDS quickSort) true) :named id0f06c55a3b9f4f8a89a028018d295ae2C_1))
(assert (! (= (isRole sorter) true) :named id0f06c55a3b9f4f8a89a028018d295ae2C_2))
(assert (! (= (consumes binarySearch sorter) true) :named id0f06c55a3b9f4f8a89a028018d295ae2C_3))
(assert (! (= (provides quickSort sorter) true) :named id0f06c55a3b9f4f8a89a028018d295ae2C_4))
(assert (! (and (= (pre binarySearch quickSort sorter) true) (= (pre quickSort binarySearch sorter) true)) :named id0f06c55a3b9f4f8a89a028018d295ae2C_5))

; Step 2

; [[#106bbb2bacfc4924843c2762bbc018efC]]
(assert (! (= (isDS binarySearch) true) :named id106bbb2bacfc4924843c2762bbc018efC_0))
(assert (! (= (isRole sorter) true) :named id106bbb2bacfc4924843c2762bbc018efC_1))
(assert (! (= (consumes binarySearch sorter) true) :named id106bbb2bacfc4924843c2762bbc018efC_2))

; [[unknowntest]]
(assert (! (exists ((test Atom) ) (and (= (isDS test) true)  (pre test binarySearch sorter))) :named idunknowntest_0))


(check-sat)
(get-unsat-core)
(get-model)
