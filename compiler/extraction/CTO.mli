open Ast
open Names
open Provenance

type ('a, 'n) cto_type =
| CTOBoolean of 'a
| CTOString of 'a
| CTODouble of 'a
| CTOLong of 'a
| CTOInteger of 'a
| CTODateTime of 'a
| CTOClassRef of 'a * 'n
| CTOOption of 'a * ('a, 'n) cto_type
| CTOArray of 'a * ('a, 'n) cto_type

type ('a, 'n) cto_declaration_desc =
| CTOEnum of char list list
| CTOTransaction of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list
| CTOConcept of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list
| CTOEvent of is_abstract * 'n extends * (char list * ('a, 'n) cto_type) list
| CTOAsset of is_abstract * 'n extends * (char list * ('a, 'n) cto_type) list
| CTOParticipant of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list

type ('a, 'n) cto_declaration = { cto_declaration_annot : 'a;
                                  cto_declaration_name : local_name;
                                  cto_declaration_type : ('a, 'n)
                                                         cto_declaration_desc }

type ('a, 'n) cto_package = { cto_package_annot : 'a;
                              cto_package_file : char list;
                              cto_package_prefix : char list;
                              cto_package_namespace : namespace_name;
                              cto_package_imports : 'a import_decl list;
                              cto_package_declarations : ('a, 'n)
                                                         cto_declaration list }

type lrcto_type = (provenance, relative_name) cto_type

type lrcto_declaration_desc = (provenance, relative_name) cto_declaration_desc

type lrcto_declaration = (provenance, relative_name) cto_declaration

type lrcto_package = (provenance, relative_name) cto_package
