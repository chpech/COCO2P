path :=
  Directory(Concatenation(PackageInfo("coco2p")[1].InstallationPath, "/doc"));
main := "coco.xml";
files := [];
bookname := "MyBook";

MakeGAPDocDoc( path, main, files, bookname );
