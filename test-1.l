[Preamble]
[#b873e31aef6940b0a669c9396ab74334P]
IsInt(maxSize);

[#f4bd16aef3574779933fe8f401677852P]
IsDS(quickSort);
Provides(quickSort, sorter);
IsAttrDS(AD.quickSort.status);
HasAttr(quickSort, AD.quickSort.status);
AD.quickSort.status == verified;
IsAttrDS(AD.quickSort.avgSpeed);
HasAttr(quickSort, AD.quickSort.avgSpeed);
AD.quickSort.avgSpeed == 100;
IsAttrDS(AD.quickSort.outputOrdered);
HasAttr(quickSort, AD.quickSort.outputOrdered);
AD.quickSort.outputOrdered == true;
;

[#aa702698de2f4d6c8d02aab815927412P]
IsRole(sorter);

[#ebe31fd2b90d4ecc9fbce1b877fbebf7P]
IsString(status);

[#a2f5bdfb28bd4ed88b60ea84b0d36ae3P]
IsInt(avgSpeed);

[#c79a350115a8447abd1440069a2da6baP]
IsBool(outputOrdered);

[#28833594b1cf4d11b9d44c2362064f36P]
IsDS(mergeSort);
Provides(mergeSort, sorter);
IsAttrDS(AD.mergeSort.status);
HasAttr(mergeSort, AD.mergeSort.status);
AD.mergeSort.status == verified;
IsAttrDS(AD.mergeSort.avgSpeed);
HasAttr(mergeSort, AD.mergeSort.avgSpeed);
AD.mergeSort.avgSpeed == 201;
IsAttrDS(AD.mergeSort.outputOrdered);
HasAttr(mergeSort, AD.mergeSort.outputOrdered);
AD.mergeSort.outputOrdered == true;
;

[#49feba5cb84446138e2f055c3fc509a1P]
IsRole(sorter);

[#cf71c9c3fe8749b3a4c43f00e02eaf5bP]
IsString(status);

[#69c92b8488bd4c3bb07755496efbba50P]
IsInt(avgSpeed);

[#03b38fc3d2dd41a0b912350a1323fda8P]
IsBool(outputOrdered);

[#f9161725a13a4372a974b59892256c8cP]
IsDS(binarySearch);
Consumes(binarySearch, sorter);
Provides(binarySearch, searcher);
IsAttrDS(AD.binarySearch.status);
HasAttr(binarySearch, AD.binarySearch.status);
AD.binarySearch.status == verified;
;

[#9159c26970f648749a3a4280fd02aa75P]
IsRole(sorter);

[#bff83358185b4e69a4f74a9a8fc824d4P]
IsRole(searcher);

[#c499a8a9e8734dc6aa74d178c12f9b1cP]
IsString(status);


maxSize == 500;[#f4bd16aef3574779933fe8f401677852C]
Precondition(quickSort, sorter, maxSize <= 500);
;

[#28833594b1cf4d11b9d44c2362064f36C]
Precondition(mergeSort, sorter, maxSize <= 500);
;

[#f9161725a13a4372a974b59892256c8cC]
Precondition(binarySearch, sorter, (^avgSpeed < 200) and (^outputOrdered == true));
;

FORALL ds1:DS,ds2:DS,a:AttrDS { IsString(a) and NameOf(a, "status") and Uses(ds1, ds2) implies a == "verified" };

$$$
[#b84315649ddb4f1c840b9b1be728c8ffC]
IsDS(binarySearch);
 IsDS(quickSort);
 IsRole(searcher);
 Consumes(binarySearch, searcher);
 Provides(quickSort, searcher);
 Bond(binarySearch, quickSort, searcher);


