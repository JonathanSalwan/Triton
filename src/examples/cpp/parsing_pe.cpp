/*
** Output
**
**  > parsing_pe.exe %WINDIR%\System32\notepad.exe
**  ------------------------------------------------------------------------------------------
**  File Header
**  ------------------------------------------------------------------------------------------
**  machine:              014c
**  numberOfSections:     0005
**  timeDateStamp:        57898fb0
**  pointerToSymbolTable: 00000000
**  numberOfSymbolTable:  00000000
**  sizeOfOptionalHeader: 00e0
**  characteristics:      0102
**  
**  ------------------------------------------------------------------------------------------
**  Optional Header
**  ------------------------------------------------------------------------------------------
**  magic:                       010b
**  majorLinkerVersion:          0e
**  minorLinkerVersion:          00
**  sizeOfCode:                  0001a200
**  sizeOfInitializedData:       00020600
**  sizeOfUninitializedData:     00000000
**  addressOfEntryPoint:         0001a410
**  baseOfCode:                  00001000
**  baseOfData:                  0001c000
**  imageBase:                   00400000
**  sectionAlignment:            00001000
**  fileAlignment:               00000200
**  majorOperatingSystemVersion: 000a
**  minorOperatingSystemVersion: 0000
**  majorImageVersion:           000a
**  minorImageVersion:           0000
**  majorSubsystemVersion:       000a
**  minorSubsystemVersion:       0000
**  win32VersionValue:           00000000
**  sizeOfImage:                 0003e000
**  sizeOfHeaders:               00000400
**  checkSum:                    0003ab19
**  subsystem:                   0002
**  dllCharacteristics:          c140
**  sizeOfStackReserve:          00040000
**  sizeOfStackCommit:           00011000
**  sizeOfHeapReserve:           00100000
**  sizeOfHeapCommit:            00001000
**  loaderFlags:                 00000000
**  numberOfRvaAndSizes:         00000010
**  
**  ------------------------------------------------------------------------------------------
**  Data Directories
**  ------------------------------------------------------------------------------------------
**                             RVA     Size
**  exportTable             00000000 00000000
**  importTable             0001f4b8 00000244
**  resourceTable           00022000 00019ce0
**  exceptionTable          00000000 00000000
**  certificateTable        00000000 00000000
**  baseRelocationTable     0003c000 00001c50
**  debugTable              00004450 00000038
**  architectureTable       00000000 00000000
**  globalPtr               00000000 00000000
**  tlsTable                00000000 00000000
**  loadConfigTable         000012a8 00000080
**  boundImportTable        00000000 00000000
**  importAddressTable      0001f000 000004b4
**  delayImportDescriptor   00000000 00000000
**  clrRuntimeHeader        00000000 00000000
**  
**  ------------------------------------------------------------------------------------------
**  Seaction Headers
**  ------------------------------------------------------------------------------------------
**              RVA     VSize   RawAddr RawSize  ptrReloc ptrLineN nRlc nLin  chrstc
**     .text 0001a0a4 00001000 0001a200 00000400 00000000 00000000 0000 0000 60000020
**     .data 000026a4 0001c000 00000800 0001a600 00000000 00000000 0000 0000 c0000040
**    .idata 00002054 0001f000 00002200 0001ae00 00000000 00000000 0000 0000 40000040
**     .rsrc 00019ce0 00022000 00019e00 0001d000 00000000 00000000 0000 0000 40000040
**    .reloc 00001c50 0003c000 00001e00 00036e00 00000000 00000000 0000 0000 42000040
**
** ... (imports/exports section)
*/

#include <iostream>
#include <triton/api.hpp>
#include <triton/abstractBinary.hpp>



int main(int ac, const char *av[]) {
  triton::format::AbstractBinary binary;

  if (ac != 2)
    return -1;

  binary.loadBinary(av[1]);

  auto pe = binary.getPE();

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "File Header" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << std::hex << std::setfill('0');
  auto fhdr = pe->getHeader().getFileHeader();
  std::cout << "machine:              " << std::setw(4) << fhdr.machine << std::endl;
  std::cout << "numberOfSections:     " << std::setw(4) << fhdr.numberOfSections << std::endl;
  std::cout << "timeDateStamp:        " << std::setw(8) << fhdr.timeDateStamp << std::endl;
  std::cout << "pointerToSymbolTable: " << std::setw(8) << fhdr.pointerToSymbolTable << std::endl;
  std::cout << "numberOfSymbolTable:  " << std::setw(8) << fhdr.numberOfSymbolTable << std::endl;
  std::cout << "sizeOfOptionalHeader: " << std::setw(4) << fhdr.sizeOfOptionalHeader << std::endl;
  std::cout << "characteristics:      " << std::setw(4) << fhdr.characteristics << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Optional Header" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  auto ohdr = pe->getHeader().getOptionalHeader();
  std::cout << std::hex;
  std::cout << "magic:                       " << std::setw(4) << ohdr.magic << std::endl;
  std::cout << "majorLinkerVersion:          " << std::setw(2) << int(ohdr.majorLinkerVersion) << std::endl;
  std::cout << "minorLinkerVersion:          " << std::setw(2) << int(ohdr.minorLinkerVersion) << std::endl;
  std::cout << "sizeOfCode:                  " << std::setw(8) << ohdr.sizeOfCode << std::endl;
  std::cout << "sizeOfInitializedData:       " << std::setw(8) << ohdr.sizeOfInitializedData << std::endl;
  std::cout << "sizeOfUninitializedData:     " << std::setw(8) << ohdr.sizeOfUninitializedData << std::endl;
  std::cout << "addressOfEntryPoint:         " << std::setw(8) << ohdr.addressOfEntryPoint << std::endl;
  std::cout << "baseOfCode:                  " << std::setw(8) << ohdr.baseOfCode << std::endl;
  std::cout << "baseOfData:                  " << std::setw(8) << ohdr.baseOfData << std::endl;
  std::cout << "imageBase:                   " << std::setw(8) << ohdr.imageBase << std::endl;
  std::cout << "sectionAlignment:            " << std::setw(8) << ohdr.sectionAlignment << std::endl;
  std::cout << "fileAlignment:               " << std::setw(8) << ohdr.fileAlignment << std::endl;
  std::cout << "majorOperatingSystemVersion: " << std::setw(4) << ohdr.majorOperatingSystemVersion << std::endl;
  std::cout << "minorOperatingSystemVersion: " << std::setw(4) << ohdr.minorOperatingSystemVersion << std::endl;
  std::cout << "majorImageVersion:           " << std::setw(4) << ohdr.majorImageVersion << std::endl;
  std::cout << "minorImageVersion:           " << std::setw(4) << ohdr.minorImageVersion << std::endl;
  std::cout << "majorSubsystemVersion:       " << std::setw(4) << ohdr.majorSubsystemVersion << std::endl;
  std::cout << "minorSubsystemVersion:       " << std::setw(4) << ohdr.minorSubsystemVersion << std::endl;
  std::cout << "win32VersionValue:           " << std::setw(8) << ohdr.win32VersionValue << std::endl;
  std::cout << "sizeOfImage:                 " << std::setw(8) << ohdr.sizeOfImage << std::endl;
  std::cout << "sizeOfHeaders:               " << std::setw(8) << ohdr.sizeOfHeaders << std::endl;
  std::cout << "checkSum:                    " << std::setw(8) << ohdr.checkSum << std::endl;
  std::cout << "subsystem:                   " << std::setw(4) << ohdr.subsystem << std::endl;
  std::cout << "dllCharacteristics:          " << std::setw(4) << ohdr.dllCharacteristics << std::endl;
  std::cout << "sizeOfStackReserve:          " << std::setw(8) << ohdr.sizeOfStackReserve << std::endl;
  std::cout << "sizeOfStackCommit:           " << std::setw(8) << ohdr.sizeOfStackCommit << std::endl;
  std::cout << "sizeOfHeapReserve:           " << std::setw(8) << ohdr.sizeOfHeapReserve << std::endl;
  std::cout << "sizeOfHeapCommit:            " << std::setw(8) << ohdr.sizeOfHeapCommit << std::endl;
  std::cout << "loaderFlags:                 " << std::setw(8) << ohdr.loaderFlags << std::endl;
  std::cout << "numberOfRvaAndSizes:         " << std::setw(8) << ohdr.numberOfRvaAndSizes << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Data Directories" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "                           RVA     Size" << std::endl;
  auto ddir = pe->getHeader().getDataDirectory();
  std::cout << "exportTable             " << std::setw(8) << ddir.exportTable_rva
                                   << " " << std::setw(8) << ddir.exportTable_size << std::endl;
  std::cout << "importTable             " << std::setw(8) << ddir.importTable_rva
                                   << " " << std::setw(8) << ddir.importTable_size << std::endl;
  std::cout << "resourceTable           " << std::setw(8) << ddir.resourceTable_rva
                                   << " " << std::setw(8) << ddir.resourceTable_size << std::endl;
  std::cout << "exceptionTable          " << std::setw(8) << ddir.exceptionTable_rva
                                   << " " << std::setw(8) << ddir.exceptionTable_size << std::endl;
  std::cout << "certificateTable        " << std::setw(8) << ddir.certificateTable_rva
                                   << " " << std::setw(8) << ddir.certificateTable_size << std::endl;
  std::cout << "baseRelocationTable     " << std::setw(8) << ddir.baseRelocationTable_rva
                                   << " " << std::setw(8) << ddir.baseRelocationTable_size << std::endl;
  std::cout << "debugTable              " << std::setw(8) << ddir.debugTable_rva
                                   << " " << std::setw(8) << ddir.debugTable_size << std::endl;
  std::cout << "architectureTable       " << std::setw(8) << ddir.architectureTable_rva
                                   << " " << std::setw(8) << ddir.architectureTable_size << std::endl;
  std::cout << "globalPtr               " << std::setw(8) << ddir.globalPtr_rva
                                   << " " << std::setw(8) << ddir.globalPtr_size << std::endl;
  std::cout << "tlsTable                " << std::setw(8) << ddir.tlsTable_rva
                                   << " " << std::setw(8) << ddir.tlsTable_size << std::endl;
  std::cout << "loadConfigTable         " << std::setw(8) << ddir.loadConfigTable_rva
                                   << " " << std::setw(8) << ddir.loadConfigTable_size << std::endl;
  std::cout << "boundImportTable        " << std::setw(8) << ddir.boundImportTable_rva
                                   << " " << std::setw(8) << ddir.boundImportTable_size << std::endl;
  std::cout << "importAddressTable      " << std::setw(8) << ddir.importAddressTable_rva
                                   << " " << std::setw(8) << ddir.importAddressTable_size << std::endl;
  std::cout << "delayImportDescriptor   " << std::setw(8) << ddir.delayImportDescriptor_rva
                                   << " " << std::setw(8) << ddir.delayImportDescriptor_size << std::endl;
  std::cout << "clrRuntimeHeader        " << std::setw(8) << ddir.clrRuntimeHeader_rva
                                   << " " << std::setw(8) << ddir.clrRuntimeHeader_size << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Seaction Headers" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "            RVA     VSize   RawAddr RawSize  ptrReloc ptrLineN nRlc nLin  chrstc" << std::endl;
  for (auto section : pe->getHeader().getSectionHeaders()) {
    std::cout << std::setfill(' ') << std::setw(8) << section.name << std::setfill('0');
    std::cout << " " << std::setw(8) << section.virtualSize;
    std::cout << " " << std::setw(8) << section.virtualAddress;
    std::cout << " " << std::setw(8) << section.rawSize;
    std::cout << " " << std::setw(8) << section.rawAddress;
    std::cout << " " << std::setw(8) << section.pointerToRelocations;
    std::cout << " " << std::setw(8) << section.pointerToLinenumbers;
    std::cout << " " << std::setw(4) << section.numberOfRelocations;
    std::cout << " " << std::setw(4) << section.numberOfLinenumbers;
    std::cout << " " << std::setw(8) << section.characteristics;
    std::cout << std::endl;
  }
  std::cout << std::endl;
  if (pe->getHeader().getSectionHeaders().size() == 0)
    std::cout << std::endl << std::setw(55) << "<section header empty!>" << std::endl << std::endl;

  auto impt = pe->getImportTable();
  if (0<impt.size()) {
      std::cout << std::endl;
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      std::cout << "Import table" << std::endl;
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      for (auto impd : impt) {
          std::cout << "importLookupTableRVA  " << std::setw(8) << impd.importLookupTableRVA << std::endl;
          std::cout << "timeDateStamp         " << std::setw(8) << impd.timeDateStamp << std::endl;
          std::cout << "forwarderChain        " << std::setw(8) << impd.forwarderChain << std::endl;
          std::cout << "nameRVA               " << std::setw(8) << impd.nameRVA << std::endl;
          std::cout << "name                  " << std::setw(8) << impd.name << std::endl;
          std::cout << "importAddressTableRVA " << std::setw(8) << impd.importAddressTableRVA << std::endl;
          for (auto impe : impd.entries) {
              if (impe.importByName) {
                std::cout << "    (hint " << std::setw(4) << impe.ordinalNumber;
                std::cout << ") " << impe.name << std::endl;
              } else {
                std::cout << "    ordinalNumber " << std::setw(4) << impe.ordinalNumber << std::endl;
              }
          }
          std::cout << std::endl;
      }
      std::cout << std::endl;
  }
  auto expt = pe->getExportTable();
  if (0<ddir.exportTable_rva) {
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      std::cout << "Export table" << std::endl;
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      
      std::cout << "exportFlags            " << std::setw(8) << expt.exportFlags << std::endl;
      std::cout << "timeDateStamp          " << std::setw(8) << expt.timeDateStamp << std::endl;
      std::cout << "majorVersion           " << std::setw(4) << expt.majorVersion << std::endl;
      std::cout << "minorVersion           " << std::setw(4) << expt.minorVersion << std::endl;
      std::cout << "nameRVA                " << std::setw(8) << expt.nameRVA << std::endl;
      std::cout << "name                   " << expt.name << std::endl;
      std::cout << "ordinalBase            " << std::setw(8) << expt.ordinalBase << std::endl;
      std::cout << "addressTableEntries    " << std::setw(8) << expt.addressTableEntries << std::endl;
      std::cout << "numberOfNamePointers   " << std::setw(8) << expt.numberOfNamePointers << std::endl;
      std::cout << "exportAddressTableRVA  " << std::setw(8) << expt.exportAddressTableRVA << std::endl;
      std::cout << "namePointerRVA         " << std::setw(8) << expt.namePointerRVA << std::endl;
      std::cout << "ordinalTableRVA        " << std::setw(8) << expt.ordinalTableRVA << std::endl;
      std::cout << std::endl;
      
      std::cout << "    Ord    RVA    nameRVA  name -> fwd " << std::endl;
      for (auto expd : expt.entries) {
          std::cout << "    " << std::setw(4) << expd.ordinal;
          if (expd.isForward)
             std::cout << " " << std::setw(8) << expd.forwarderRVA;
          else
             std::cout << " " << std::setw(8) << expd.exportRVA;
          std::cout << " " << std::setw(8) << expd.exportNameRVA;
          std::cout << " " << expd.exportName;
          if (expd.isForward)
            std::cout << " -> " << expd.forwarderName;
          std::cout << std::endl;
      }
      std::cout << std::endl;
  }
  return 0;
}

