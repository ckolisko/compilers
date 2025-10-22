// Copyright (c) 2021-2023, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include <cassert>
#include "node_base.h"

NodeBase::NodeBase()
  // TODO: initialize member variables (e.g., pointer to Symbol)
{
}

NodeBase::~NodeBase() {
}


void NodeBase::setSymbol(SymbolKind kind, const std::string &name, std::shared_ptr<Type> type, SymbolTable *symtab){
  this->sym_ptr = new Symbol(kind, name, type, symtab);
}

Symbol* NodeBase::getSymbol(){
  return this->sym_ptr;
}
std::shared_ptr<Type> NodeBase::getType(){
  if (this->getSymbol()){
      return this->getSymbol()->get_type();
  } else {
    return nullptr;
  }
}




// TODO: implement member functions
