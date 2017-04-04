//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <fstream>
#include <new>

#include <triton/abstractBinary.hpp>
#include <triton/elf.hpp>
#include <triton/exceptions.hpp>
#include <triton/pe.hpp>



namespace triton {
  namespace format {

    AbstractBinary::AbstractBinary() {
      this->format = triton::format::BINARY_INVALID;
      this->binary = nullptr;
    }


    AbstractBinary::AbstractBinary(const std::string& path) {
      this->format = triton::format::BINARY_INVALID;
      this->binary = nullptr;
      this->loadBinary(path);
    }


    AbstractBinary::~AbstractBinary() {
      delete this->binary;
    }


    triton::format::binary_e AbstractBinary::getFormat(void) const {
      return this->format;
    }


    void AbstractBinary::loadBinary(const std::string& path) {
      triton::uint8 raw[8] = {0};

      // Open the file
      std::ifstream ifs(path, std::ifstream::binary);

      ifs.unsetf(std::ios::skipws);

      if (!ifs)
        throw triton::exceptions::Format("AbstractBinary::loadBinary(): Cannot open the binary file.");

      ifs.read(reinterpret_cast<char*>(raw), sizeof(raw));

      if(!ifs)
        throw triton::exceptions::Format("AbstractBinary::loadBinary(): Cannot read the file binary.");

      // Set the binary format according the magic number
      if ((*((triton::uint32*)(raw))) == triton::format::MAGIC_ELF)
        this->format = triton::format::BINARY_ELF;

      else if ((*((triton::uint32*)(raw))) == triton::format::MAGIC_MACHO32)
        this->format = triton::format::BINARY_MACHO;

      else if ((*((triton::uint32*)(raw))) == triton::format::MAGIC_MACHO64)
        this->format = triton::format::BINARY_MACHO;

      else if ((*((triton::uint16*)(raw))) == triton::format::MAGIC_PE)
        this->format = triton::format::BINARY_PE;

      else
        this->format = triton::format::BINARY_INVALID;

      // Parse the binary according to the format
      this->parseBinary(path);
    }


    void AbstractBinary::parseBinary(const std::string& path) {
      switch (this->format) {
        case triton::format::BINARY_ELF:
          delete this->binary;
          this->binary = new(std::nothrow) triton::format::elf::Elf(path);
          if (!this->binary)
            throw triton::exceptions::Format("AbstractBinary::parseBinary(): Not enough memory.");
          break;

        case triton::format::BINARY_PE:
          delete this->binary;
          this->binary = new(std::nothrow) triton::format::pe::Pe(path);
          if (!this->binary)
            throw triton::exceptions::Format("AbstractBinary::parseBinary(): Not enough memory.");
          break;

        // TODO
        case triton::format::BINARY_MACHO:
        default:
          throw triton::exceptions::Format("AbstractBinary::parseBinary(): Unsupported binary format.");
      }
    }


    triton::format::BinaryInterface* AbstractBinary::getBinary(void) {
      return this->binary;
    }


    triton::format::elf::Elf* AbstractBinary::getElf(void) {
      if (this->format != triton::format::BINARY_ELF)
        throw triton::exceptions::Format("AbstractBinary::getElf(): The abstract binary is not an ELF.");
      return reinterpret_cast<triton::format::elf::Elf*>(this->binary);
    }


    triton::format::pe::Pe* AbstractBinary::getPe(void) {
      if (this->format != triton::format::BINARY_PE)
        throw triton::exceptions::Format("AbstractBinary::getPe(): The abstract binary is not a PE.");
      return reinterpret_cast<triton::format::pe::Pe*>(this->binary);
    }


    const std::string& AbstractBinary::getPath(void) const {
      if (!this->binary)
        throw triton::exceptions::Format("AbstractBinary::getPath(): You must load the binary before.");
      return this->binary->getPath();
    }


    const std::list<triton::format::MemoryMapping>& AbstractBinary::getMemoryMapping(void) const {
      if (!this->binary)
        throw triton::exceptions::Format("AbstractBinary::getMemoryMapping(): You must load the binary before.");
      return this->binary->getMemoryMapping();
    }

  }; /* format namespace */
}; /* triton namespace */
