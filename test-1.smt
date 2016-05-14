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
   (and (= p0 binarySearch) (= p1 quickSort) (= p2 searcher))
  ) true false))
(define-fun isBool ((p0 Atom) ) Bool  (if (or 
   (= p0 outputOrdered)
  ) true false))
(define-fun provides ((p0 Atom) (p1 Atom) ) Bool  (if (or 
   (and (= p0 quickSort) (= p1 sorter))
   (and (= p0 quickSort) (= p1 searcher))
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
   (and (= p0 binarySearch) (= p1 searcher))
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
    (if (<= (valueOf maxSize )  500) true false) (if 
  (and (= owner mergeSort) (= role sorter))
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

; [[Preamble, #b873e31aef6940b0a669c9396ab74334P]]
(assert (! (= (isInt maxSize) true) :named idb873e31aef6940b0a669c9396ab74334P_0))

; [[#f4bd16aef3574779933fe8f401677852P]]
(assert (! (= (isDS quickSort) true) :named idf4bd16aef3574779933fe8f401677852P_0))
(assert (! (= (provides quickSort sorter) true) :named idf4bd16aef3574779933fe8f401677852P_1))
(assert (! (= (isAttrDS AD.quickSort.status) true) :named idf4bd16aef3574779933fe8f401677852P_2))
(assert (! (= (hasAttr quickSort AD.quickSort.status) true) :named idf4bd16aef3574779933fe8f401677852P_3))
(assert (! (= (valueOf AD.quickSort.status )   (valueOf verified ) ) :named idf4bd16aef3574779933fe8f401677852P_4))
(assert (! (= (isAttrDS AD.quickSort.avgSpeed) true) :named idf4bd16aef3574779933fe8f401677852P_5))
(assert (! (= (hasAttr quickSort AD.quickSort.avgSpeed) true) :named idf4bd16aef3574779933fe8f401677852P_6))
(assert (! (= (valueOf AD.quickSort.avgSpeed )  100) :named idf4bd16aef3574779933fe8f401677852P_7))
(assert (! (= (isAttrDS AD.quickSort.outputOrdered) true) :named idf4bd16aef3574779933fe8f401677852P_8))
(assert (! (= (hasAttr quickSort AD.quickSort.outputOrdered) true) :named idf4bd16aef3574779933fe8f401677852P_9))
(assert (! (= (valueOf AD.quickSort.outputOrdered )   (valueOf string0 ) ) :named idf4bd16aef3574779933fe8f401677852P_10))

; [[#aa702698de2f4d6c8d02aab815927412P]]
(assert (! (= (isRole sorter) true) :named idaa702698de2f4d6c8d02aab815927412P_0))

; [[#ebe31fd2b90d4ecc9fbce1b877fbebf7P]]
(assert (! (= (isString status) true) :named idebe31fd2b90d4ecc9fbce1b877fbebf7P_0))

; [[#a2f5bdfb28bd4ed88b60ea84b0d36ae3P]]
(assert (! (= (isInt avgSpeed) true) :named ida2f5bdfb28bd4ed88b60ea84b0d36ae3P_0))

; [[#c79a350115a8447abd1440069a2da6baP]]
(assert (! (= (isBool outputOrdered) true) :named idc79a350115a8447abd1440069a2da6baP_0))

; [[#28833594b1cf4d11b9d44c2362064f36P]]
(assert (! (= (isDS mergeSort) true) :named id28833594b1cf4d11b9d44c2362064f36P_0))
(assert (! (= (provides mergeSort sorter) true) :named id28833594b1cf4d11b9d44c2362064f36P_1))
(assert (! (= (isAttrDS AD.mergeSort.status) true) :named id28833594b1cf4d11b9d44c2362064f36P_2))
(assert (! (= (hasAttr mergeSort AD.mergeSort.status) true) :named id28833594b1cf4d11b9d44c2362064f36P_3))
(assert (! (= (valueOf AD.mergeSort.status )   (valueOf verified ) ) :named id28833594b1cf4d11b9d44c2362064f36P_4))
(assert (! (= (isAttrDS AD.mergeSort.avgSpeed) true) :named id28833594b1cf4d11b9d44c2362064f36P_5))
(assert (! (= (hasAttr mergeSort AD.mergeSort.avgSpeed) true) :named id28833594b1cf4d11b9d44c2362064f36P_6))
(assert (! (= (valueOf AD.mergeSort.avgSpeed )  201) :named id28833594b1cf4d11b9d44c2362064f36P_7))
(assert (! (= (isAttrDS AD.mergeSort.outputOrdered) true) :named id28833594b1cf4d11b9d44c2362064f36P_8))
(assert (! (= (hasAttr mergeSort AD.mergeSort.outputOrdered) true) :named id28833594b1cf4d11b9d44c2362064f36P_9))
(assert (! (= (valueOf AD.mergeSort.outputOrdered )   (valueOf string0 ) ) :named id28833594b1cf4d11b9d44c2362064f36P_10))

; [[#49feba5cb84446138e2f055c3fc509a1P]]
(assert (! (= (isRole sorter) true) :named id49feba5cb84446138e2f055c3fc509a1P_0))

; [[#cf71c9c3fe8749b3a4c43f00e02eaf5bP]]
(assert (! (= (isString status) true) :named idcf71c9c3fe8749b3a4c43f00e02eaf5bP_0))

; [[#69c92b8488bd4c3bb07755496efbba50P]]
(assert (! (= (isInt avgSpeed) true) :named id69c92b8488bd4c3bb07755496efbba50P_0))

; [[#03b38fc3d2dd41a0b912350a1323fda8P]]
(assert (! (= (isBool outputOrdered) true) :named id03b38fc3d2dd41a0b912350a1323fda8P_0))

; [[#f9161725a13a4372a974b59892256c8cP]]
(assert (! (= (isDS binarySearch) true) :named idf9161725a13a4372a974b59892256c8cP_0))
(assert (! (= (consumes binarySearch sorter) true) :named idf9161725a13a4372a974b59892256c8cP_1))
(assert (! (= (provides binarySearch searcher) true) :named idf9161725a13a4372a974b59892256c8cP_2))
(assert (! (= (isAttrDS AD.binarySearch.status) true) :named idf9161725a13a4372a974b59892256c8cP_3))
(assert (! (= (hasAttr binarySearch AD.binarySearch.status) true) :named idf9161725a13a4372a974b59892256c8cP_4))
(assert (! (= (valueOf AD.binarySearch.status )   (valueOf verified ) ) :named idf9161725a13a4372a974b59892256c8cP_5))

; [[#9159c26970f648749a3a4280fd02aa75P]]
(assert (! (= (isRole sorter) true) :named id9159c26970f648749a3a4280fd02aa75P_0))

; [[#bff83358185b4e69a4f74a9a8fc824d4P]]
(assert (! (= (isRole searcher) true) :named idbff83358185b4e69a4f74a9a8fc824d4P_0))

; [[#c499a8a9e8734dc6aa74d178c12f9b1cP]]
(assert (! (= (isString status) true) :named idc499a8a9e8734dc6aa74d178c12f9b1cP_0))
(assert (! (= (valueOf maxSize )  500) :named idc499a8a9e8734dc6aa74d178c12f9b1cP_1))

; [[#f9161725a13a4372a974b59892256c8cC]]
(assert (! (forall ((ds1 Atom) (ds2 Atom) (a Atom) ) (=> (and (= (isAttrDS a) true) (= (isDS ds2) true) (= (isDS ds1) true) ) (=> (and (and (= (isString a) true) (= (nameOf a) string1)) (= (uses ds1 ds2) true)) (= (valueOf a )   (valueOf string2 ) )))) :named idf9161725a13a4372a974b59892256c8cC_0))


(check-sat)
(get-unsat-core)
(get-model)
