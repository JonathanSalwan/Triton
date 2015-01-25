//
//  Jonathan Salwan - 2015-01-24
// 
//  http://shell-storm.org
//  http://twitter.com/JonathanSalwan
// 
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software  Foundation, either  version 3 of  the License, or
//  (at your option) any later version.
//

#include "pin.H"
#include "dse.h"


VOID notImplemented(std::string insDis, ADDRINT insAddr)
{
  if (_analysisStatus == LOCKED)
    return;

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % "n/a" % "n/a (Not Implemented)";
}

