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
#include <algorithm>

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


Node *SemanticAnalysis::promote_to_int(Node *n) {
  assert(n->getType().get()->is_integral());
  assert(n->getType().get()->get_basic_type_kind() < BasicTypeKind::INT);
  
  std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::INT, n->getType()->is_signed());
  return implicit_conversion(n, type);
}

Node *SemanticAnalysis::promote_to_long(Node *n) {
  assert(n->getType().get()->is_integral());
  assert(n->getType().get()->get_basic_type_kind() < BasicTypeKind::LONG);
  
  std::shared_ptr<Type> type = std::make_shared<BasicType>(BasicTypeKind::LONG, n->getType()->is_signed());
  return implicit_conversion(n, type);
}

Node *SemanticAnalysis::promote_to_unsigned(Node *n) {
  assert(n->getType().get()->is_integral());
  assert(n->getType().get()->is_signed());
  
  std::shared_ptr<Type> type = std::make_shared<BasicType>(n->getType()->get_basic_type_kind(), false);
  return implicit_conversion(n, type);
}

Node *SemanticAnalysis::implicit_conversion(Node *n, std::shared_ptr<Type> type) {
  std::unique_ptr<Node> conversion( new Node(AST_IMPLICIT_CONVERSION, {n}));
  conversion->setSymbol(SymbolKind::TYPE, n->getSymbol()->get_name() , type, this->m_cur_symtab);
  return conversion.release();
}


void SemanticAnalysis::visit_struct_type(Node *n) {
  // Here, we want to lookup the struct type in the symbol table.
  std::string structName = "struct " + n->get_kid(0)->get_str();
  Symbol* sym_ptr = this->m_cur_symtab->lookup_recursive(structName);
  if (!sym_ptr){
    SemanticError::raise(n->get_loc(),"Undefined struct reference.");
  }
  n->setSymbol(sym_ptr);
}

void SemanticAnalysis::visit_union_type(Node *n) {
  RuntimeError::raise("union types aren't supported");
}

// Ident, * declare, declare [arraysize]
void SemanticAnalysis::visit_variable_declaration(Node *n) {
  // Go to child for base type.
  visit(n->get_kid(1));
  // Go through the declarators list, add to table.
  Node *decl_list = n->get_kid(2);
  for (auto i = decl_list->cbegin(); i != decl_list->cend(); ++i) {
    Node *declarator = *i;
    declarator->setDecType(n->get_kid(1)->getType());
    visit(declarator);
    this->m_cur_symtab->add_entry(declarator->get_loc(), SymbolKind::VARIABLE, declarator->getSymbol()->get_name(), declarator->getType());
    n->structMembers.push_back(Member(declarator->getSymbol()->get_name() , declarator->getType()));
  }
  // Need to return a nice type and string structs, so the symbol will just be the declared type.
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
      SemanticError::raise(n->get_loc(), "invalid basic type");
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


// Get the qualifiers, if any.
bool getQual(Node* n, TypeQualifier* qual){
  Node* curNode = n->get_kid(0);
  if (curNode == nullptr){
    SemanticError::raise(n->get_loc(), "Basic type node has no kids");
  }
  std::string qualString = curNode->get_str(); 
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
    case ERRORSTATE:
    {
        std::string errorString = "Invalid basic type ";
        SemanticError::raise(n->get_loc(), "%s", errorString.c_str());
    }
    case VOIDSTATE:
    if (hasQual){
      SemanticError::raise(n->get_loc(),"Can't use void with a qualifier.");
    }
    type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::VOID, true));
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
  std::shared_ptr<Type> base_type = n->getDecType();
  n->setSymbol(SymbolKind::VARIABLE, n->get_kid(0)->get_str(), base_type, this->m_cur_symtab);
}

// Pointer to base type.
void SemanticAnalysis::visit_pointer_declarator(Node *n) {
  // Wrap in pointer type. Wrap on the way down, not up.

  // No matter what, pass the kid the type and our current pointer wrapped type.
  std::shared_ptr<Type> our_type;
  our_type =std::shared_ptr<Type>( new PointerType(n->getDecType()));

  n->get_kid(0)->setDecType(our_type);
  visit(n->get_kid(0));

  // Then set the nodes type as whatever was calced as named declarator.
  n->setSymbol(SymbolKind::VARIABLE, n->get_kid(0)->getSymbol()->get_name(), n->get_kid(0)->getType(), this->m_cur_symtab);
}

//Array base type.
void SemanticAnalysis::visit_array_declarator(Node *n) {
  // Wrap in array type, pass down.

  // No matter what, pass the kid the type and our current pointer wrapped type.
  std::shared_ptr<Type> our_type;
  our_type = std::shared_ptr<Type>( new ArrayType(n->getDecType(), std::stoi(n->get_kid(1)->get_str())));

  n->get_kid(0)->setDecType(our_type);
  visit(n->get_kid(0));

  // Then set the nodes type as whatever was calced as named declarator.
  n->setSymbol(SymbolKind::VARIABLE, n->get_kid(0)->getSymbol()->get_name(), n->get_kid(0)->getType(), this->m_cur_symtab);
}

// Check if al; parts of this function def / dec is matching the current one.
void SemanticAnalysis::checkRedef(Node *n){

  // Check if the return type is the same.
  visit(n->get_kid(0));
  
  std::shared_ptr<Type> baseType = n->get_kid(0)->getType();
  if (baseType.get()->get_basic_type_kind() != this->m_cur_symtab->get_fn_type().get()->get_base_type().get()->get_basic_type_kind() ){
    SemanticError::raise(n->get_loc(), "Non matching return types.");
  }

  // Check the number of params.
  unsigned numKids = n->get_kid(2)->get_num_kids();
  if (numKids != this->m_cur_symtab->get_num_parameters() ) {
    SemanticError::raise(n->get_loc(), "Non matching number of parameters.");
  }
  
  SymbolTable * curTable = this->m_cur_symtab;
  
  Node* paramNode = n->get_kid(2);
  for (unsigned i = 0; i < numKids; i++){
    visit(paramNode->get_kid(i));
    std::shared_ptr<Type> curType = paramNode->get_kid(i)->getType();
    std::shared_ptr<Type> tableType = curTable->get_fn_type().get()->get_member(i).get_type();
    if (curType.get()->get_basic_type_kind() != tableType.get()->get_basic_type_kind()) {
      SemanticError::raise(n->get_loc(), "Non matching parameters types.");
    } 
  }
  // If the params matched up, great.
}

// Make an entry in the table, make new symtab, visit kids.
void SemanticAnalysis::visit_function_definition(Node *n) { 

  // First, the name for redef check.
  std::string funcName =  n->get_kid(1)->get_str();

  // Check if we have already defined.
  SymbolTable *fn_symtab = nullptr;  
  
  for (std::vector<SymbolTable*>::iterator it = this->m_all_symtabs.begin(); it != this->m_all_symtabs.end(); it++){
    if ((*it)->get_name() == "function " + funcName){
      fn_symtab = *it;
    }
  }
  if (fn_symtab){
    this->m_cur_symtab = fn_symtab; 
    checkRedef(n);
    return;
  } 

  // Not defined, so we are going to make a new table.

  // First, get the base (return) type
  visit(n->get_kid(0));
  std::shared_ptr<Type> baseType = n->get_kid(0)->getType();
  std::shared_ptr<FunctionType> funcType = std::shared_ptr<FunctionType>(new FunctionType(baseType));

  // Visit param and statement list with new symbol table.
  SymbolTable* funcTable = this->enter_scope("function " + funcName);
  funcTable->set_fn_type(funcType);

  // Process the param list, add the members to the base type.
  int numKids = n->get_kid(2)->get_num_kids();
  Node* paramNode = n->get_kid(2);
  for (int i = 0; i < numKids; i++){
    visit(paramNode->get_kid(i));
    std::shared_ptr<Type> parType = paramNode->get_kid(i)->getType();
    parType.get()->as_str();
    const Member mem = Member(paramNode->get_kid(i)->getSymbol()->get_name(), parType); 
    funcType.get()->add_member(mem);
    std::string entName = paramNode->get_kid(i)->get_kid(1)->get_kid(0)->get_str();

    // Can finally add the params to the symbol table.
    this->m_cur_symtab->add_entry(paramNode->get_kid(i)->get_loc(), SymbolKind::VARIABLE, paramNode->get_kid(i)->getSymbol()->get_name(), parType);
  }

  // Process statements
  n->get_kid(3)->setDefiner(true);
  visit(n->get_kid(3));
  this->leave_scope();
  
  // Add function to global table.
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, funcName, funcType);
}

// Similar to function definition, just no body after. Make sure to use same names.
void SemanticAnalysis::visit_function_declaration(Node *n) {
  // First, get the base (return) type
  visit(n->get_kid(0));
  std::shared_ptr<Type> baseType = n->get_kid(0)->getType();
  std::shared_ptr<FunctionType> funcType = std::shared_ptr<FunctionType>(new FunctionType(baseType));
  // Next, the name.
  std::string funcName = n->get_kid(1)->get_str();

  // Make new symbol table for the function.
  SymbolTable* funcTable = this->enter_scope("function " +funcName);
  funcTable->set_fn_type(funcType);

  // Process the param list, add the members to the base type.
  int numKids = n->get_kid(2)->get_num_kids();
  Node* paramNode = n->get_kid(2);

  // Put these params in function's table.
  for (int i = 0; i < numKids; i++){
    visit(paramNode->get_kid(i));
    std::shared_ptr<Type> parType = paramNode->get_kid(i)->getType();
    const Member mem = Member(paramNode->get_kid(i)->getSymbol()->get_name(), parType); 
    funcType.get()->add_member(mem);
    
    // Can finally add the params to the symbal table.
    this->m_cur_symtab->add_entry(paramNode->get_kid(i)->get_loc(), SymbolKind::VARIABLE, paramNode->get_kid(i)->getSymbol()->get_name(), parType);
  }

  this->leave_scope();

  // Add function to global table.
  this->m_cur_symtab->add_entry(n->get_loc(), SymbolKind::FUNCTION, funcName, funcType);
}

// Process param list into a hasMembers type.
// Make the sym table entries for them as well.
void SemanticAnalysis::visit_function_parameter_list(Node *n) {
}

void SemanticAnalysis::visit_function_parameter(Node *n) {
  visit(n->get_kid(0)); // First, do our basic type node.
  // This is named declarator. Give it the type info.
  n->get_kid(1)->setDecType(n->get_kid(0)->getType());
  visit(n->get_kid(1));
  Symbol* sym_ptr = n->get_kid(1)->getSymbol();
  if (sym_ptr->get_type().get()->is_array()) { // If we have an array, convert to pointer.
    std::shared_ptr<Type>  ptrType = std::shared_ptr<Type>( new PointerType(sym_ptr->get_type().get()->get_base_type()));
    n->setSymbol(SymbolKind::VARIABLE, sym_ptr->get_name(), ptrType, this->m_cur_symtab);
    n->get_kid(1)->setSymbol(SymbolKind::VARIABLE, sym_ptr->get_name(), ptrType, this->m_cur_symtab);
  }else {
    n->setSymbol(sym_ptr);
  }
}

void SemanticAnalysis::visit_statement_list(Node *n) {
  // Ok so we want to just visit all kids basically.
  // But also need to change scope if within statement list already.
  // Check if node has special tag
  bool definer = n->getDefiner();
  if (!definer){
    std::string tabName = "block " + std::to_string(n->get_loc().get_line());
    this->enter_scope(tabName);  
  }

  int numKids =  n->get_num_kids();
  for (int i = 0; i < numKids; i++)
  {
    visit(n->get_kid(i));
  }

  if (!definer){
    this->leave_scope();
  }
}

void SemanticAnalysis::visit_return_expression_statement(Node *n) {
  // Get the type that is being returned.
  visit(n->get_kid(0));
  // Compare the type to the ret type of the function.
  // Similar to assign in a way.
  Symbol * sym = n->get_kid(0)->getSymbol();
  std::shared_ptr<Type> funType =  this->m_cur_symtab->get_fn_type();
  if (! sym->get_type().get()->is_same(funType.get()->get_base_type().get())) {
    SemanticError::raise(n->get_loc(),"Hey that's the wrong return type.");
  } 
}

void SemanticAnalysis::visit_struct_type_definition(Node *n) {
  std::string name = n->get_kid(0)->get_str();
Location loc = n->get_loc();
std::shared_ptr<Type> struct_type = std::shared_ptr<StructType>(new StructType(name));

m_cur_symtab->add_entry(loc, SymbolKind::TYPE, "struct " + name, struct_type);

// Ok so we want to just visit all kids of the second child basically.
// But also need to change scope for struct.
std::string structName = "struct " + name;
this->enter_scope(structName);  

Node * fieldList = n->get_kid(1);

int numKids =  fieldList->get_num_kids();
for (int i = 0; i < numKids; i++)
{
  visit(fieldList->get_kid(i));
  for (std::vector<Member>::iterator it = fieldList->get_kid(i)->structMembers.begin(); it != fieldList->get_kid(i)->structMembers.end(); it++){
    struct_type.get()->add_member(*(it));
  }
}

this->leave_scope();
}

// Check if this symbol satisfies an lval.
void checkLval(Symbol* sym, Location loc){

// Check if ref to var
if (sym->get_kind() == SymbolKind::VARIABLE){
  // Array check.
  if (sym->get_type().get()->is_array()){
    std::string errorString = "Can't assign to an array";
    SemanticError::raise(loc, "%s", errorString.c_str());
  }

  return;
} else if (sym->get_kind() == SymbolKind::TYPE){
  if (sym->get_type().get()->is_struct()){
    return;
  }
  std::string errorString = "Can't assign to a type unless a struct.";
  SemanticError::raise(loc, "%s", errorString.c_str());
  return;
} else {
  std::string errorString = "Can't assign a value to a function";
  SemanticError::raise(loc, "%s", errorString.c_str());
  }
}

// Checks if this assignment operation will be valid.
void checkAssign (Type* t1, Type* t2, Location l1){

  //Special case for 2 pointers.
  if (t1->is_pointer() ){
    if (t2->is_pointer() || t2->is_array()){
      //Check they have same unqualified base types.
      if (t1->get_unqualified_type()->is_same(t2->get_unqualified_type())){
        //Check if base on left has all quals right side has.
        std::shared_ptr<Type> b1 = t1->get_base_type();
        std::shared_ptr<Type> b2 = t2->get_base_type();
        if (b2.get()->is_const()){
          if (!b1.get()->is_const()){
            SemanticError::raise(l1, "Right side is not const.");    
          }
        }
        if (b2.get()->is_volatile()){
          if (!b1.get()->is_volatile()){
            SemanticError::raise(l1, "Right side is not volatile.");
          }
        }
      }
    } else {
      SemanticError::raise(l1,"Can't assign a pointer and non-pointer");
    }
    return;
  }

  // Okay now we just have nice variable values.
  if(t1->is_const()) {
    SemanticError::raise(l1, "CANNOT have const get assigned on left!");
  }

  // If right side is pointer, no.
  if (t2->is_pointer()){
    SemanticError::raise(l1, "Can't assign pointer to non pointer value.");
    return;
  }
  // If right side is void, no.
  if (t2->is_void()){
    SemanticError::raise(l1, "Can't assign void to something.");
    return;
  }

  // If we have struct on left, we better have a struct on the right. and vice versa.
  if (t1->is_struct() != t2->is_struct()){
    SemanticError::raise(l1, "CANNOT have stuct and non struct assignment!");
  }

}

// Check / promote nodes to int.
// Error if it does not make sense
void SemanticAnalysis::processLogical(Node* n){
  if (n->getType().get()->is_integral()) {
      if (n->getType().get()->get_basic_type_kind() < BasicTypeKind::INT) {
        n = this->promote_to_int(n);
      }
  } else {
    SemanticError::raise(n->get_loc(), "Can't do this operation on non integral type.");
  }
}


void SemanticAnalysis::visit_binary_expression(Node *n) {
  // Do a little bit of error checking using the symbol table.
  // First child is the expression, second var ref, third either literal or another ref.
  int tokOp = n->get_kid(0)->get_tag();
  // Lets visit the kids first to populate their types.
  Node * kid1 = n->get_kid(1);
  Node * kid2 = n->get_kid(2);
  visit(kid1);
  visit(kid2);

  switch (tokOp)
  {
  case TOK_ASSIGN:
    checkLval(kid1->getSymbol(), kid1->get_loc());
    if (kid2->getType() == nullptr){
      return;
    }
    checkAssign(kid1->getType().get(), kid2->getType().get(), kid1->get_loc());
    break;
  case TOK_LOGICAL_OR:
  case TOK_LOGICAL_AND:
  case TOK_GT:
  case TOK_GTE:
  case TOK_LT:
  case TOK_LTE:
  case TOK_EQUALITY:
  case TOK_INEQUALITY:
  {
    processLogical(kid1);
    processLogical(kid2);
    // If we processed both, we are an int value now.
    Symbol* sym = new Symbol(SymbolKind::TYPE, kid1->getSymbol()->get_name() + " op " + kid2->getSymbol()->get_name(), kid1->getSymbol()->get_type(), this->m_cur_symtab);
    n->setSymbol(sym);
  }
  break;
  case TOK_MINUS: // Plus and minus are special because pointers.
  case TOK_PLUS:
  if (kid1->getType().get()->is_pointer() != kid2->getType().get()->is_pointer()) { // Only one is a pointer
    if (kid1->getType().get()->is_pointer()) { // Snag that pointer type and set it.
      processLogical(kid2);
      n->setSymbol(kid1->getSymbol()); 
    } else {
      processLogical(kid1);
      n->setSymbol(kid2->getSymbol());
    }
    break;
  }
  case TOK_DIVIDE: //Otherwise, normal math.
  case TOK_ASTERISK:
  if (kid1->getType().get()->is_pointer() || kid2->getType().get()->is_pointer()) {// NO
    SemanticError::raise(n->get_loc(), "Invalid operation with pointers");
  } 

  
  {
    processLogical(kid1);
    processLogical(kid2);
    // Now, to process the sign precision (long or int), and the signedness.
    BasicTypeKind t1 = kid1->getType().get()->get_basic_type_kind();
    BasicTypeKind t2 = kid2->getType().get()->get_basic_type_kind();
    BasicTypeKind mostPrecise = BasicTypeKind::INT;
    bool signedness = true;
    if (t1 < t2) { // t1 - int, t2 - long
      this->promote_to_long(kid1);
      mostPrecise = BasicTypeKind::LONG;
    } else if (t2 < t1) { // t1 - long, t2 - int
      this->promote_to_long(kid2);
      mostPrecise = BasicTypeKind::LONG;
    }
    // Signness conversions.
    bool s1 = kid1->getType().get()->is_signed();
    bool s2 = kid2->getType().get()->is_signed();
    if (s1 && !s2) { // s1 - signed, s2 - unsigned
      this->promote_to_unsigned(kid1);
      signedness = false;
    } else if (!s1 && s2) { // s1 - unsigned, s2 - signed
      this->promote_to_unsigned(kid2);
      signedness = false;
    }

    // If we processed both, we are an integral value now.
    // Need to be highest.
    std::shared_ptr<Type> newType = std::shared_ptr<BasicType>(new BasicType(mostPrecise, signedness));
    Symbol* sym = new Symbol(SymbolKind::TYPE, kid1->getSymbol()->get_name() + " op " + kid2->getSymbol()->get_name(), newType, this->m_cur_symtab);
    n->setSymbol(sym);
  }
  break;
  

  default:
    break;
  }

}


void SemanticAnalysis::visit_unary_expression(Node *n) {
  // Handle *, &, !, and -
  // Get the op, handle seperately.
  int tok = n->get_kid(0)->get_tag();
  Node *kid = n->get_kid(1);
  visit(kid);
  switch (tok)
  {
  case TOK_ASTERISK: // Deref by one, if possible.
    if (kid->getSymbol()->get_type().get()->is_pointer()){
      std::shared_ptr<Type> base = kid->getSymbol()->get_type().get()->get_base_type();
      n->setSymbol(kid->getSymbol()->get_kind(), base.get()->as_str(), base,this->m_cur_symtab);
    } else {
      SemanticError::raise(n->get_loc(), "Can't dereference non-pointer");
    }
  break;
  case TOK_AMPERSAND: // Process, then wrap in pointer.
  {  
    // Check if value is non lvalue..
    checkLval(kid->getSymbol(), kid->get_loc());
    std::shared_ptr<Type> base = std::shared_ptr<Type>( new PointerType(kid->getSymbol()->get_type()));
    n->setSymbol(SymbolKind::VARIABLE, base.get()->as_str(), base, this->m_cur_symtab);
    break;
  } 
  case TOK_MINUS: // Promote to into or unsigned int.
    if (kid->getType().get()->is_integral()) {
      if (kid->getType().get()->get_basic_type_kind() < BasicTypeKind::INT) {
        kid = this->promote_to_int(kid);
      }
      // Okay, now we can just set the symbol as what the kid is now.
      n->setSymbol(kid->getSymbol());

    } else {
      SemanticError::raise(n->get_loc(), "Can't do unary arithmetic on non integral");
    }
    break;
  case TOK_NOT: // Check if the symbol is not 0 basically. Does convert to int.
    if (kid->getType().get()->is_integral()) {
      if (kid->getType().get()->get_basic_type_kind() < BasicTypeKind::INT) {
        kid = this->promote_to_int(kid);
      }
      // Okay, now we can just set the symbol as what the kid is now.
      n->setSymbol(kid->getSymbol());

    } else {
      SemanticError::raise(n->get_loc(), "Can't do unary not on non integral");
    }
  break;
  default:
    break;
  }
}

void SemanticAnalysis::visit_postfix_expression(Node *n) {
}

void SemanticAnalysis::visit_conditional_expression(Node *n) {
}

void SemanticAnalysis::visit_cast_expression(Node *n) {
}

void SemanticAnalysis::visit_function_call_expression(Node *n) {
  // Process child 0, the function name.
  visit(n->get_kid(0));

  // Now, process the args list. Do same checks as function def and declare.
  Node * argList = n->get_kid(1);
  int numKids = argList->get_num_kids();
  std::shared_ptr<Type> baseType = n->get_kid(0)->getType().get()->get_base_type();
  int expectNumArgs = n->get_kid(0)->getType().get()->get_num_members();
  if (expectNumArgs != numKids){
    SemanticError::raise(n->get_loc(), "Mismatching number of arguments.");
  }
  // Check if each param is good.
  for(int i = 0; i < numKids; i++){ 
    visit(argList->get_kid(i));
    std::shared_ptr<Type> t1 = n->get_kid(0)->getType().get()->get_member(i).get_type();
    std::shared_ptr<Type> t2 = argList->get_kid(i)->getType();
    checkAssign(t1.get(), t2.get(), n->get_loc());
    // Need to check if we can convert the kid type into t1 
  }

  // Okay, now assign this node symbol with the base type, like it is returning a value.
  Symbol* sym = new Symbol(SymbolKind::TYPE, n->get_kid(0)->getType().get()->get_base_type().get()->as_str(), n->get_kid(0)->getType().get()->get_base_type(), this->m_cur_symtab);
  n->setSymbol(sym);
  
}

// Like when you do f.x . Ref the x field in f. 
// Lets look up f in the symbol table, then use that to process x.
// End of day, we want to get x symbol.
// But, can be points[i].x
void SemanticAnalysis::visit_field_ref_expression(Node *n) {
  n->isStructRef = true;
  visit(n->get_kid(0)); // Process struct.
  // get matching member, check if we match this.
  
  std::shared_ptr<Type> baseType;
  baseType = n->get_kid(0)->getType();

  // If we have a pointer here, we err.
  if (baseType.get()->is_pointer()){
    SemanticError::raise(n->get_loc(), "DO NOT try to use dot on a pointer.");
  }
  // Otherwise, it is a struct pretty much.
  const Member* match = baseType.get()->find_member(n->get_kid(1)->get_str());
  if (!match){ //No match
    std::string errorString = "No field " + n->get_kid(1)->get_str() + " found in struct.";
    SemanticError::raise(n->get_loc(), "%s", errorString.c_str());
  }
  // If there was match, great. Set type.
  n->setSymbol(SymbolKind::VARIABLE, match->get_name(),match->get_type(),this->m_cur_symtab);
}

// This is for those v->s type things. Like above
// Do NOT allow arr[0].
void SemanticAnalysis::visit_indirect_field_ref_expression(Node *n) {
  visit(n->get_kid(0)); // Process struct or array pointer. f->d
  // get matching member, check if we matches this.
  std::shared_ptr<Type> baseType;
  baseType = n->get_kid(0)->getType();
  
  // Crunch through pointer
  std::shared_ptr<Type> ptrBaseType = baseType.get()->get_base_type();

  // Now, just a struct.
  const Member* match = ptrBaseType.get()->find_member(n->get_kid(1)->get_str());
  if (!match){ //No match
    std::string errorString = "No field " + n->get_kid(1)->get_str() + " found in struct.";
    SemanticError::raise(n->get_loc(), "%s", errorString.c_str());
  }

  // If there was match, great. Set type.
  n->setSymbol(SymbolKind::VARIABLE, match->get_name(),match->get_type(),this->m_cur_symtab);
}

void SemanticAnalysis::visit_array_element_ref_expression(Node *n) {
  // Just like a regular var except we visit kids down to get the name back in symbol form.
  n->isArrayRef = true;
  visit(n->get_kid(0));
  Symbol* sym;
  if (n->get_kid(0)->isArrayRef) { // In this case, no table lookup for sym, just pull sym from kid.
    sym = n->get_kid(0)->getSymbol();
  } else if (n->get_kid(0)->isStructRef) { // Just rip it out of that array eing reffed.
    sym = n->get_kid(0)->getSymbol();
  } else {
    // Also we need to look it up in the symbol's table.
    sym = this->m_cur_symtab->lookup_recursive(n->get_kid(0)->getSymbol()->get_name());
  }
  std::shared_ptr<Type> base = sym->get_type().get()->get_base_type();
  n->setSymbol(SymbolKind::VARIABLE, n->get_kid(0)->getSymbol()->get_name(), base, this->m_cur_symtab);
  // CANNOT yank here. But I have to.

}

void SemanticAnalysis::visit_variable_ref(Node *n) {
  // All we want to do is make sure it exists in the symbol table, and get the symbol.
  n->setSymbol(this->m_cur_symtab->lookup_recursive(n->get_kid(0)->get_str()));
}

void SemanticAnalysis::visit_literal_value(Node *n) {
  // Ok, so we want togive this literal a type.
  // n->setSymbol(SymbolKind::VARIABLE, n->get_kid(0)->getSymbol()->get_name(), base, this->m_cur_symtab);
  std::shared_ptr<Type> type;
  
  switch (n->get_kid(0)->get_tag())
  {
  {
  case TOK_INT_LIT:
  LiteralValue val = LiteralValue::from_int_literal (n->get_kid(0)->get_str(), n->get_loc());
    if (val.is_long() && val.is_unsigned() ){
      type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::LONG, false));
    } else if (val.is_long()){
      type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::LONG, true));
    } else if (val.is_unsigned()){
      type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::INT, false));
    } else {
      type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::INT, true));
    }
    break;
  }
  case TOK_CHAR_LIT:
    type = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::CHAR, true));
    break;
  case TOK_STR_LIT:
  {
    std::shared_ptr<Type> base = std::shared_ptr<BasicType>(new BasicType(BasicTypeKind::CHAR, true));
    type = std::shared_ptr<PointerType>(new PointerType(base));
    break;
  }
  default:
    break;
  }
  n->setSymbol(SymbolKind::TYPE, n->get_kid(0)->get_str(), type, this->m_cur_symtab);
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

