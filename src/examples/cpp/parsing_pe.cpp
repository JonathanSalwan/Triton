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
**  Section Headers
**  ------------------------------------------------------------------------------------------
**              RVA     VSize   RawAddr RawSize  ptrReloc ptrLineN nRlc nLin  chrstc
**     .text 0001a0a4 00001000 0001a200 00000400 00000000 00000000 0000 0000 60000020
**     .data 000026a4 0001c000 00000800 0001a600 00000000 00000000 0000 0000 c0000040
**    .idata 00002054 0001f000 00002200 0001ae00 00000000 00000000 0000 0000 40000040
**     .rsrc 00019ce0 00022000 00019e00 0001d000 00000000 00000000 0000 0000 40000040
**    .reloc 00001c50 0003c000 00001e00 00036e00 00000000 00000000 0000 0000 42000040
**
**  ------------------------------------------------------------------------------------------
**  Import table
**  ------------------------------------------------------------------------------------------
**  importLookupTableRVA  0001f6fc
**  timeDateStamp         00000000
**  forwarderChain        00000000
**  nameRVA               0001fcaa
**  name                  ADVAPI32.dll
**  importAddressTableRVA 0001f000
**      (hint 0214) OpenProcessToken
**      (hint 016f) GetTokenInformation
**      (hint 00ee) DuplicateEncryptionInfoFile
**      (hint 02a6) RegSetValueExW
**      (hint 0296) RegQueryValueExW
**      (hint 0264) RegCreateKeyW
**      (hint 0258) RegCloseKey
**      (hint 0289) RegOpenKeyExW
**      (hint 0121) EventSetInformation
**      (hint 0120) EventRegister
**      (hint 0122) EventUnregister
**      (hint 0128) EventWriteTransfer
**      (hint 0197) IsTextUnicode
**  ...
*/

#include <iostream>
#include <triton/api.hpp>
#include <triton/abstractBinary.hpp>



int main(int ac, const char *av[]) {
  triton::format::AbstractBinary binary;

  if (ac != 2)
    return -1;

  try {
    binary.loadBinary(av[1]);
  } catch (const std::exception &e) {
      std::cerr << e.what();
      return 1;
  }

  auto pe = binary.getPe();

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "File Header" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << std::hex << std::setfill('0');
  auto fhdr = pe->getHeader().getFileHeader();
  std::cout << "machine:              " << std::setw(4) << fhdr.getMachine() << std::endl;
  std::cout << "numberOfSections:     " << std::setw(4) << fhdr.getNumberOfSections() << std::endl;
  std::cout << "timeDateStamp:        " << std::setw(8) << fhdr.getTimeDateStamp() << std::endl;
  std::cout << "pointerToSymbolTable: " << std::setw(8) << fhdr.getPointerToSymbolTable() << std::endl;
  std::cout << "numberOfSymbolTable:  " << std::setw(8) << fhdr.getNumberOfSymbolTable() << std::endl;
  std::cout << "sizeOfOptionalHeader: " << std::setw(4) << fhdr.getSizeOfOptionalHeader() << std::endl;
  std::cout << "characteristics:      " << std::setw(4) << fhdr.getCharacteristics() << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Optional Header" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  auto ohdr = pe->getHeader().getOptionalHeader();
  std::cout << std::hex;
  std::cout << "magic:                       " << std::setw(4) << ohdr.getMagic() << std::endl;
  std::cout << "majorLinkerVersion:          " << std::setw(2) << int(ohdr.getMajorLinkerVersion()) << std::endl;
  std::cout << "minorLinkerVersion:          " << std::setw(2) << int(ohdr.getMinorLinkerVersion()) << std::endl;
  std::cout << "sizeOfCode:                  " << std::setw(8) << ohdr.getSizeOfCode() << std::endl;
  std::cout << "sizeOfInitializedData:       " << std::setw(8) << ohdr.getSizeOfInitializedData() << std::endl;
  std::cout << "sizeOfUninitializedData:     " << std::setw(8) << ohdr.getSizeOfUninitializedData() << std::endl;
  std::cout << "addressOfEntryPoint:         " << std::setw(8) << ohdr.getAddressOfEntryPoint() << std::endl;
  std::cout << "baseOfCode:                  " << std::setw(8) << ohdr.getBaseOfCode() << std::endl;
  std::cout << "baseOfData:                  " << std::setw(8) << ohdr.getBaseOfData() << std::endl;
  std::cout << "imageBase:                   " << std::setw(8) << ohdr.getImageBase() << std::endl;
  std::cout << "sectionAlignment:            " << std::setw(8) << ohdr.getSectionAlignment() << std::endl;
  std::cout << "fileAlignment:               " << std::setw(8) << ohdr.getFileAlignment() << std::endl;
  std::cout << "majorOperatingSystemVersion: " << std::setw(4) << ohdr.getMajorOperatingSystemVersion() << std::endl;
  std::cout << "minorOperatingSystemVersion: " << std::setw(4) << ohdr.getMinorOperatingSystemVersion() << std::endl;
  std::cout << "majorImageVersion:           " << std::setw(4) << ohdr.getMajorImageVersion() << std::endl;
  std::cout << "minorImageVersion:           " << std::setw(4) << ohdr.getMinorImageVersion() << std::endl;
  std::cout << "majorSubsystemVersion:       " << std::setw(4) << ohdr.getMajorSubsystemVersion() << std::endl;
  std::cout << "minorSubsystemVersion:       " << std::setw(4) << ohdr.getMinorSubsystemVersion() << std::endl;
  std::cout << "win32VersionValue:           " << std::setw(8) << ohdr.getWin32VersionValue() << std::endl;
  std::cout << "sizeOfImage:                 " << std::setw(8) << ohdr.getSizeOfImage() << std::endl;
  std::cout << "sizeOfHeaders:               " << std::setw(8) << ohdr.getSizeOfHeaders() << std::endl;
  std::cout << "checkSum:                    " << std::setw(8) << ohdr.getCheckSum() << std::endl;
  std::cout << "subsystem:                   " << std::setw(4) << ohdr.getSubsystem() << std::endl;
  std::cout << "dllCharacteristics:          " << std::setw(4) << ohdr.getDllCharacteristics() << std::endl;
  std::cout << "sizeOfStackReserve:          " << std::setw(8) << ohdr.getSizeOfStackReserve() << std::endl;
  std::cout << "sizeOfStackCommit:           " << std::setw(8) << ohdr.getSizeOfStackCommit() << std::endl;
  std::cout << "sizeOfHeapReserve:           " << std::setw(8) << ohdr.getSizeOfHeapReserve() << std::endl;
  std::cout << "sizeOfHeapCommit:            " << std::setw(8) << ohdr.getSizeOfHeapCommit() << std::endl;
  std::cout << "loaderFlags:                 " << std::setw(8) << ohdr.getLoaderFlags() << std::endl;
  std::cout << "numberOfRvaAndSizes:         " << std::setw(8) << ohdr.getNumberOfRvaAndSizes() << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Data Directories" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "                           RVA     Size" << std::endl;
  auto ddir = pe->getHeader().getDataDirectory();
  std::cout << "exportTable             " << std::setw(8) << ddir.getExportTable_rva()
                                   << " " << std::setw(8) << ddir.getExportTable_size() << std::endl;
  std::cout << "importTable             " << std::setw(8) << ddir.getImportTable_rva()
                                   << " " << std::setw(8) << ddir.getImportTable_size() << std::endl;
  std::cout << "resourceTable           " << std::setw(8) << ddir.getResourceTable_rva()
                                   << " " << std::setw(8) << ddir.getResourceTable_size() << std::endl;
  std::cout << "exceptionTable          " << std::setw(8) << ddir.getExceptionTable_rva()
                                   << " " << std::setw(8) << ddir.getExceptionTable_size() << std::endl;
  std::cout << "certificateTable        " << std::setw(8) << ddir.getCertificateTable_rva()
                                   << " " << std::setw(8) << ddir.getCertificateTable_size() << std::endl;
  std::cout << "baseRelocationTable     " << std::setw(8) << ddir.getBaseRelocationTable_rva()
                                   << " " << std::setw(8) << ddir.getBaseRelocationTable_size() << std::endl;
  std::cout << "debugTable              " << std::setw(8) << ddir.getDebugTable_rva()
                                   << " " << std::setw(8) << ddir.getDebugTable_size() << std::endl;
  std::cout << "architectureTable       " << std::setw(8) << ddir.getArchitectureTable_rva()
                                   << " " << std::setw(8) << ddir.getArchitectureTable_size() << std::endl;
  std::cout << "globalPtr               " << std::setw(8) << ddir.getGlobalPtr_rva()
                                   << " " << std::setw(8) << ddir.getGlobalPtr_size() << std::endl;
  std::cout << "tlsTable                " << std::setw(8) << ddir.getTlsTable_rva()
                                   << " " << std::setw(8) << ddir.getTlsTable_size() << std::endl;
  std::cout << "loadConfigTable         " << std::setw(8) << ddir.getLoadConfigTable_rva()
                                   << " " << std::setw(8) << ddir.getLoadConfigTable_size() << std::endl;
  std::cout << "boundImportTable        " << std::setw(8) << ddir.getBoundImportTable_rva()
                                   << " " << std::setw(8) << ddir.getBoundImportTable_size() << std::endl;
  std::cout << "importAddressTable      " << std::setw(8) << ddir.getImportAddressTable_rva()
                                   << " " << std::setw(8) << ddir.getImportAddressTable_size() << std::endl;
  std::cout << "delayImportDescriptor   " << std::setw(8) << ddir.getDelayImportDescriptor_rva()
                                   << " " << std::setw(8) << ddir.getDelayImportDescriptor_size() << std::endl;
  std::cout << "clrRuntimeHeader        " << std::setw(8) << ddir.getClrRuntimeHeader_rva()
                                   << " " << std::setw(8) << ddir.getClrRuntimeHeader_size() << std::endl;
  std::cout << std::endl;

  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "Section Headers" << std::endl;
  std::cout << "------------------------------------------------------------------------------------------" << std::endl;
  std::cout << "            RVA     VSize   RawAddr RawSize  ptrReloc ptrLineN nRlc nLin  chrstc" << std::endl;
  for (auto section : pe->getHeader().getSectionHeaders()) {
    std::cout << std::setfill(' ') << std::setw(8) << section.getName() << std::setfill('0');
    std::cout << " " << std::setw(8) << section.getVirtualAddress();
    std::cout << " " << std::setw(8) << section.getVirtualSize();
    std::cout << " " << std::setw(8) << section.getRawAddress();
    std::cout << " " << std::setw(8) << section.getRawSize();
    std::cout << " " << std::setw(8) << section.getPointerToRelocations();
    std::cout << " " << std::setw(8) << section.getPointerToLinenumbers();
    std::cout << " " << std::setw(4) << section.getNumberOfRelocations();
    std::cout << " " << std::setw(4) << section.getNumberOfLinenumbers();
    std::cout << " " << std::setw(8) << section.getCharacteristics();
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
          std::cout << "importLookupTableRVA  " << std::setw(8) << impd.getImportLookupTableRVA() << std::endl;
          std::cout << "timeDateStamp         " << std::setw(8) << impd.getTimeDateStamp() << std::endl;
          std::cout << "forwarderChain        " << std::setw(8) << impd.getForwarderChain() << std::endl;
          std::cout << "nameRVA               " << std::setw(8) << impd.getNameRVA() << std::endl;
          std::cout << "name                  " << impd.getName() << std::endl;
          std::cout << "importAddressTableRVA " << std::setw(8) << impd.getImportAddressTableRVA() << std::endl;
          for (auto impe : impd.getEntries()) {
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
  if (0<ddir.getExportTable_rva()) {
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      std::cout << "Export table" << std::endl;
      std::cout << "------------------------------------------------------------------------------------------" << std::endl;
      
      std::cout << "exportFlags            " << std::setw(8) << expt.getExportFlags() << std::endl;
      std::cout << "timeDateStamp          " << std::setw(8) << expt.getTimeDateStamp() << std::endl;
      std::cout << "majorVersion           " << std::setw(4) << expt.getMajorVersion() << std::endl;
      std::cout << "minorVersion           " << std::setw(4) << expt.getMinorVersion() << std::endl;
      std::cout << "nameRVA                " << std::setw(8) << expt.getNameRVA() << std::endl;
      std::cout << "name                   " << expt.getName() << std::endl;
      std::cout << "ordinalBase            " << std::setw(8) << expt.getOrdinalBase() << std::endl;
      std::cout << "addressTableEntries    " << std::setw(8) << expt.getAddressTableEntries() << std::endl;
      std::cout << "numberOfNamePointers   " << std::setw(8) << expt.getNumberOfNamePointers() << std::endl;
      std::cout << "exportAddressTableRVA  " << std::setw(8) << expt.getExportAddressTableRVA() << std::endl;
      std::cout << "namePointerRVA         " << std::setw(8) << expt.getNamePointerRVA() << std::endl;
      std::cout << "ordinalTableRVA        " << std::setw(8) << expt.getOrdinalTableRVA() << std::endl;
      std::cout << std::endl;
      
      std::cout << "    Ord    RVA    nameRVA  name -> fwd " << std::endl;
      for (auto expd : expt.getEntries()) {
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

