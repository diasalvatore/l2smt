[Preamble]
[#925acc4d11b445ccbba02835045812abP]
IsInt(maxSize);

[#a660d8f850804dbba7a5edbb6de76381P]
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

[#5e9771f3a4174a80af5842a898b69343P]
IsRole(sorter);

[#3b0d6faf084b4d5a94c38521d170f0b7P]
IsString(status);

[#484623c997cf450f9ddd1f2ae60740a3P]
IsInt(avgSpeed);

[#81cb091a04854c43b864673610319603P]
IsBool(outputOrdered);

[#487196ae95804376a04e2a056401be95P]
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

[#08dfab4f790b4facbafa09a6798a343cP]
IsRole(sorter);

[#9520f2ee531b430690bd34303efbceb5P]
IsString(status);

[#3d962fe14b6140dcb245fc0034b5c905P]
IsInt(avgSpeed);

[#9eceed85b84f48539c3fa45c9c8841c8P]
IsBool(outputOrdered);

[#b99e127e6ee84d72a6934921e37630a3P]
IsDS(binarySearch);
Consumes(binarySearch, sorter);
Provides(binarySearch, searcher);
IsAttrDS(AD.binarySearch.status);
HasAttr(binarySearch, AD.binarySearch.status);
AD.binarySearch.status == verified;
;

[#89e0ba57c9694199ad3ba34701b5a633P]
IsRole(sorter);

[#be69562637a54e95b94518badd0bf745P]
IsRole(searcher);

[#73323c5ca48b48f8849d91e783aea36eP]
IsString(status);


maxSize == 500;FORALL ds1:DS,ds2:DS,a:AttrDS { IsString(a) and NameOf(a, "status") and Uses(ds1, ds2) implies a == "verified" };

$$$
[#0f06c55a3b9f4f8a89a028018d295ae2C]
IsDS(binarySearch);
 Precondition(binarySearch, sorter, (^avgSpeed < 200) and (^outputOrdered == true));
IsDS(quickSort);
 Precondition(quickSort, sorter, maxSize <= 500);
IsRole(sorter);
 Consumes(binarySearch, sorter);
 Provides(quickSort, sorter);
 Bond(binarySearch, quickSort, sorter);




$$$
[#106bbb2bacfc4924843c2762bbc018efC]
IsDS(binarySearch);
 Precondition(binarySearch, sorter, (^avgSpeed < 200) and (^outputOrdered == true));
IsRole(sorter);
 Consumes(binarySearch, sorter);
 [unknown test]
EXISTS test:DS { Precondition(test, binarySearch, sorter) };

