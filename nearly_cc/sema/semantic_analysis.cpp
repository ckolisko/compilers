// Copyright (c) 2021-2024, David H. Hovemeyer <david.hovemeyer@gmail.com>
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
#include <algorithm>
#include <utility>
#include <map>
#include "grammar_symbols.h"
#include "parse.tab.h"
#include "node.h"
#include "ast.h"
#include "exceptions.h"
#include "semantic_analysis.h"
#include <iostream>

SemanticAnalysis::SemanticAnalysis(const Options &options)
  : m_options(options)
  , m_global_symtab(new SymbolTable(nullptr, "global")) {
  m_cur_symtab = m_global_symtab;
  m_all_symtabs.push_back(m_global_symtab);
}

SemanticAnalysis::~SemanticAnalysis() {
  // The semantic analyzer owns the SymbolTables and their Symbols,
  // so delete them. Note that the AST has pointers to Symbol objects,
  // so the SemanticAnalysis object should live at least as long
  // as the AST.
  for (auto i = m_all_symtabs.begin(); i != m_all_symtabs.end(); ++i)
    delete *i;
}

void SemanticAnalysis::visit_struct_type(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

// Ident, * declare, declare [arraysize]
void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // Go to child for base type.
  visit(n->get_kid(1));
  // Go through the declarators list.
  Node *decl_list = n->get_kid(2);
  for (auto i = decl_list->cbegin(); i != decl_list->cend(); ++i) {
  Node *declarator = *i;
  declarator->setSymbol(n->get_kid(1)->getSymbol());
  visit(declarator);
}
}

    enum word {
      VOIDWORD,
      INTWORD,
      CHARWORD,
      SIGNEDWORD,
      UNSIGNEDWORD,
      SHORTWORD,
      LONGWORD
    };
    enum state {
      S0,
      VOIDSTATE,
      INTSTATE,
      CHARSTATE,
      SIGNSTATE,
      LENSTATE,
      SIGNLENSTATE,
      INTSIGNSTATE,
      INTLENSTATE,
      INTSIGNLENSTATE,
      CHARSIGNSTATE,
      ERRORSTATE
    };
  enum len {
  SHORTLEN,
  LONGLEN,
  NONELEN
  };

word getWordEnum (std::string string, Location loc) {
  word word;
  if (string == "void"){
    word = word::VOIDWORD;
  } else if (string == "int"){
    word = word::INTWORD;
  } else if (string == "char"){
    word = word::CHARWORD;
  } else if (string == "signed"){
    word = word::SIGNEDWORD;
  } else if (string == "unsigned"){
    word = word::UNSIGNEDWORD;
  } else if (string == "short"){
    word = word::SHORTWORD;
  } else if (string == "long"){
    word = word::LONGWORD;
  }  else {
    SemanticError::raise(loc,"invalid basic type provided");
  } 
  return word;
}

// State machine functions take in the current word, output resulting state.
state stateMachineS0 (word curWord, len *length, bool *signVal){
  switch (curWord)
  {
  case word::VOIDWORD:
    return state::VOIDSTATE;
    break;
  case word::INTWORD:
    return state::INTSTATE;
  
  case word::CHARWORD:
    return state::CHARSTATE;
  
  case word::SIGNEDWORD:
    *signVal = true;
    return state::SIGNSTATE;
  case word::UNSIGNEDWORD:
    *signVal = false;
    return state::SIGNSTATE;
  
  case word::SHORTWORD:
      *length = len::SHORTLEN;
      return state::LENSTATE;
  case word::LONGWORD:
    *length = len::LONGLEN;
    return state::LENSTATE;

  default:
    throw RuntimeError("Somehow passed an invalid word to state function.");
  }
}

// Error state for char, int, void, 
state stateMachineINT (word curWord, len *length, bool *signVal){
  if (curWord == word::VOIDWORD || curWord == word::CHARWORD || curWord == word::INTWORD){
    return state::ERRORSTATE;
  } else {
    switch (curWord)
    {
    case word::SIGNEDWORD:
      *signVal = true;
      return state::INTSIGNSTATE;
    case word::UNSIGNEDWORD:
      *signVal = false;
      return state::INTSIGNSTATE;

    case word::SHORTWORD:
      *length = len::SHORTLEN;
      return state::INTLENSTATE;

    case word::LONGWORD:
      *length = len::LONGLEN;
      return state::INTLENSTATE;

    default:
    throw RuntimeError("Not possible, invalid word to state function.");
    }
  }
}
// Error for int, char, void, short, long
state stateMachineCHAR (word curWord, len *length, bool *signVal){
if (curWord == word::VOIDWORD || curWord == word::CHARWORD || curWord == word::INTWORD || curWord == word::SHORTWORD || curWord == word::LONGWORD){
    return state::ERRORSTATE;
  } else {
    switch (curWord)
    {
    case word::SIGNEDWORD:
      *signVal = true;
      return state::CHARSIGNSTATE;
    case word::UNSIGNEDWORD:
      *signVal = false;
      return state::CHARSIGNSTATE;

      default:
    throw RuntimeError("Not possible, invalid word to state function.");
    }
  }
}
// Error on char, void, signed, unsigned
state stateMachineSIGN (word curWord, len *length, bool *signVal){
  if (curWord == word::VOIDWORD || curWord == word::SIGNEDWORD || curWord == word::UNSIGNEDWORD){
    return state::ERRORSTATE;
  } else {
    switch (curWord)
    {
    case word::INTWORD:
      return state::INTSIGNSTATE;

    case word::CHARWORD:
      return state::CHARSIGNSTATE;

    case word::SHORTWORD:
      *length = len::SHORTLEN;
      return state::SIGNLENSTATE;

    case word::LONGWORD:
      *length = len::LONGLEN;
      return state::SIGNLENSTATE;

      default:
    throw RuntimeError("Not possible, invalid word to state function.");
    }
  }
}
// Error on long, short, void, char
state stateMachineLEN (word curWord, len *length, bool *signVal){
  if (curWord == word::VOIDWORD || curWord == word::LONGWORD || curWord == word::SHORTWORD || curWord == word::CHARWORD){
    return state::ERRORSTATE;
  } else {
    switch (curWord)
    {
    case word::INTWORD:
      return state::INTLENSTATE;

    case word::SIGNEDWORD:
      *signVal = true;
      return state::SIGNLENSTATE ;
    case word::UNSIGNEDWORD:
      *signVal = false;
      return state::SIGNLENSTATE ;

    default:
    throw RuntimeError("Not possible, invalid word to state function.");
      break;
    }
  }
}

// Error on anything but LEN
state stateMachineINTSIGN (word curWord, len *length, bool *signVal){
  if (curWord == word::SHORTWORD){
    *length = len::SHORTLEN;
  } else if (curWord == word::LONGWORD){
    *length = len::LONGLEN;
  } else {
    return state::ERRORSTATE;
  }
  return state::INTSIGNLENSTATE;
}

// Error on anything but sign.
state stateMachineINTLEN (word curWord, len *length, bool *signVal){
  if (curWord == word::SIGNEDWORD ){
    *signVal = true;
  } else if (curWord == word::UNSIGNEDWORD) {
    *signVal = false;
  } else {
    return state::ERRORSTATE;
  }
  return state::INTSIGNLENSTATE;
}

// Given a node n, gets the end state of the basic type.
state getEndState(Node* n, len *length, bool *signVal, bool hasQual){
    int numKids = n->get_num_kids();

    state curState = state::S0;
    std::string runningWord; // For errors
    std::string curString;  //Current word being looked at
    Node* curNode; // Current child node. Declared out here for error state case.

    // In any order.
    int startIndex = 0;
    if (hasQual && numKids < 2) {
      SemanticError(n->get_loc(), "invalid basic type");
    } else if (hasQual){
      startIndex = 1;
    }
    for (int i = startIndex; i < numKids; i++){

      // If we hit error state, tell them their invalid string.
      if (curState == state::ERRORSTATE || curState == state::INTSIGNLENSTATE || curState == state::CHARSIGNSTATE){
        std::string errorString = "Invalid basic type: " + runningWord;
        SemanticError::raise(curNode->get_loc(), "%s", errorString.c_str());
      }
      
      curNode = n->get_kid(i);
      std::string curString = curNode->get_str();
      word curWord = getWordEnum(curString, curNode->get_loc());

      // We doing a state machine. States are above. 
      // Just pass word to current state's function, get back next state.
      switch (curState) {
      case state::S0 :
        curState = stateMachineS0(curWord, length, signVal);
      break;
      case state::VOIDSTATE :
      {
        // Instantly invalid.
        std::string errorString = "Invalid basic type: " + runningWord;
        SemanticError::raise(curNode->get_loc(), "%s",errorString.c_str());
      }
        break;
      case state::INTSTATE :
        curState = stateMachineINT(curWord, length, signVal);
      break;
      case state::CHARSTATE :
        curState = stateMachineCHAR(curWord, length, signVal);
      break;
      case state::SIGNSTATE :
        curState = stateMachineSIGN(curWord, length, signVal);
      break;
      case state::LENSTATE :
        curState = stateMachineLEN(curWord, length, signVal);
      break;
      case state::INTSIGNSTATE :
        curState = stateMachineINTSIGN(curWord, length, signVal);
      break;
      case state::INTLENSTATE :
        curState = stateMachineINTLEN(curWord, length, signVal);
      break;
      default: // This ain't good..
        std::string errorString = "This shouldn't be possible, but this string broke it: " + runningWord;
        SemanticError::raise(curNode->get_loc(), "%s",errorString.c_str());
      break;
      }
    }
    return curState;

}


// Get the qualifier, if any.
bool getQual(Node* n, TypeQualifier* qual){
  Node* curNode = n->get_kid(0);
  if (curNode == nullptr){
    SemanticError::raise(n->get_loc(), "Basic type node has no kids");
  }
  std::string qualString =curNode->get_str(); 
  if (qualString == "const") {
    *qual =  TypeQualifier::CONST;
    return true;
  } else if (qualString == "volatile" ){
    *qual =  TypeQualifier::VOLATILE;
    return true;
  }
  return false;
}

//Analyze char, int, void, long, short, signed, unsigned.
// Annotate node with its final state.
void SemanticAnalysis::visit_basic_type(Node *n) {
  // Check for qualifier
  bool hasQual = false;
  
  TypeQualifier qual; 
  if (getQual(n, &qual)){
    hasQual = true;
  } 

  len length = len::NONELEN;
  bool signVal = true; 
  state endState = getEndState(n, &length, &signVal, hasQual);
  // Now we interpret the end state and annotate, which means another switch case.
  std::shared_ptr<BasicType> type;

  switch (endState)
  {
    case VOIDSTATE:
    type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::VOID, false));
    break;
    case CHARSTATE:
    case CHARSIGNSTATE:
    type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::CHAR, signVal));
    break;
    case INTSTATE:
    case SIGNSTATE:
    case INTSIGNSTATE:
    type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::INT, signVal));
    break;
    case LENSTATE:
    case INTLENSTATE:
    case SIGNLENSTATE:
    case INTSIGNLENSTATE:
    if (length == len::LONGLEN){
          type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::LONG, signVal));
    } else {
      type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::SHORT, signVal));
    }
    break;

  default:
    throw RuntimeError("reached invalid end state");
    break;
  }
  // If we have qual, wrap basic type up.
  std::shared_ptr<QualifiedType> qualType;
  
  if (hasQual) {
    qualType = std::shared_ptr<QualifiedType>(new QualifiedType(type, qual));
    n->setSymbol(SymbolKind::TYPE, "qualified basic type", qualType, this->m_cur_symtab);
  } else {
    n->setSymbol(SymbolKind::TYPE, "basic type", type, this->m_cur_symtab);
  }
}

// This is the classic identifier.
void SemanticAnalysis::visit_named_declarator(Node *n) {
  std::shared_ptr<Type> base_type = n->getType();
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::VARIABLE, n->get_kid(0)->get_str(), base_type);
}

// Pointer to base type.
void SemanticAnalysis::visit_pointer_declarator(Node *n) {
  // Wrap in pointer type
  std::shared_ptr<Type> base_type =std::shared_ptr<Type>( new PointerType(n->getType() ));
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::VARIABLE, n->get_kid(0)->get_kid(0)->get_str(), base_type);
}

//Array base type.
void SemanticAnalysis::visit_array_declarator(Node *n) {
  // Wrap in pointer type
  std::shared_ptr<Type> base_type =std::shared_ptr<Type>( new ArrayType(n->getType(), std::stoi(n->get_kid(1)->get_str())));
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::VARIABLE, n->get_kid(0)->get_kid(0)->get_str(), base_type);
}

// Make an entry in the table, make new symtab, visit kids.
void SemanticAnalysis::visit_function_definition(Node *n) {
  // First, get the base (return) type
  visit(n->get_kid(0));
  std::shared_ptr<Type> baseType = n->get_kid(0)->getType();
  std::shared_ptr<FunctionType> funcType = std::shared_ptr<FunctionType>(new FunctionType(baseType));
  // Next, the name.
  std::string funcName = n->get_kid(1)->get_str();

  // Make new symbol table for the function. 
  SymbolTable funcTable = SymbolTable(this->m_cur_symtab, "function " + funcName);

  // Process the param list, add the members to the base type.
  int numKids = n->get_kid(2)->get_num_kids();
  for (int i = 0; i < numKids; i++){
    visit(n->get_kid(i));
    std::shared_ptr<Type> parType = n->get_kid(i)->getType();
    const Member mem = Member(n->get_kid(i)->getSymbol()->get_name(), parType); 
    funcType.get()->add_member(mem);
    funcTable.add_entry(n->get_loc(),SymbolKind::VARIABLE, "p"+i, parType);
  }

  // Add function to global table.
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, funcName, funcType);

  // Visit statement list with new symbol table.
  this->enter_scope("function " + funcName);
  visit(n->get_kid(3));
  this->leave_scope();
}

void SemanticAnalysis::visit_function_declaration(Node *n) {
  // TODO: implement
}

// Process param list into a hasMembers type.
// Make the sym table entries for them as well.
void SemanticAnalysis::visit_function_parameter_list(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_statement_list(Node *n) {
  // Ok so we want to just visit all kids basically
  int numKids =  n->get_num_kids();
  for (int i = 0; i < numKids; i++)
  {
    visit(n->get_kid(i));
  }
  

}

void SemanticAnalysis::visit_return_expression_statement(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_binary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_unary_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_cast_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_function_call_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_variable_ref(Node *n) {
  // TODO: implement
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  // TODO: implement
}

SymbolTable *SemanticAnalysis::enter_scope(const std::string &name) {
  SymbolTable *symtab = new SymbolTable(m_cur_symtab, name);
  m_all_symtabs.push_back(symtab);
  m_cur_symtab = symtab;
  return symtab;
}

void SemanticAnalysis::leave_scope() {
  assert(m_cur_symtab->get_parent() != nullptr);
  m_cur_symtab = m_cur_symtab->get_parent();
}

// TODO: implement helper functions
