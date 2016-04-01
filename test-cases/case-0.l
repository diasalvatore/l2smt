[System Status]			
IsRole(R.sorter) && IsRole(R.searcher);
IsDS(DS.quickSort) && IsDS(DS.mergeSort) && IsDS(DS.binarySearch);
IsInt(AD.quickSort.size) && IsInt(AD.mergeSort.size);
IsString(AD.test.maxComponents);
IsString(AD.quickSort.status) && IsString(AD.mergeSort.status);
IsAttrDS(AD.quickSort.status) && IsAttrDS(AD.mergeSort.status);
IsAttrDS(AD.quickSort.size) && IsAttrDS(AD.mergeSort.size);
HasAttr(DS.quickSort, AD.quickSort.size) && HasAttr(DS.mergeSort, AD.mergeSort.size);
Provides(DS.quickSort, R.sorter) && Provides(DS.mergeSort, R.sorter) && Provides(DS.binarySearch, R.searcher);
Consumes(DS.binarySearch, R.searcher);



[Test]
// IsDS(R.sorter);
HasAttr(DS.mergeSort, AD.quickSort.size);
AD.quickSort.size == 70;
AD.mergeSort.size == 20;
AD.quickSort.status == "verified";
AD.mergeSort.status == "unverified"; // test
// AD.test.maxComponents == "23";
"x" == "x";
Bond(DS.binarySearch, DS.quickSort, R.searcher);

[Small Components]		
FORALL ds1:DS,ds2:DS,a:AttrDS { IsString(a) && NameOf(a, "status") => a == "verified" };
// EXISTS ds1:DS,ds2:DS,r:Role { Bond(ds1, ds2, r) }
