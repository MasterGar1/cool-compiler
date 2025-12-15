#include "CoolSemantics.h"

#include <expected>
#include <string>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <map>
#include <set>

#include "antlr4-runtime/antlr4-runtime.h"
#include "passes/TypeChecker.h"

using namespace std;
using namespace antlr4;

// Data structures for semantic information
struct Formal {
    string name;
    string type;
};

struct Method {
    string name;
    vector<Formal> formals;
    string return_type;
};

struct Attribute {
    string name;
    string type;
};

using AttributeMap = std::map<string, Attribute>;
using MethodMap = std::map<string, Method>;

struct ClassNode {
    string name;
    string parent_name;
    CoolParser::ClassContext* context;
    AttributeMap attributes;
    MethodMap methods;
};

using ClassTable = std::map<string, ClassNode>;

string print_inheritance_loops_error(vector<vector<string>> inheritance_loops) {
    stringstream eout;
    eout << "Detected " << inheritance_loops.size() << " loops in the type hierarchy:" << endl;
    for (int i = 0; i < inheritance_loops.size(); ++i) {
        eout << i + 1 << ") ";
        for (const auto& name : inheritance_loops[i]) {
            eout << name << " <- ";
        }
        eout << endl;
    }

    return eout.str();
}

bool is_subtype(const string& child, const string& parent, const string& current_class, const ClassTable& class_table) {
    if (child == "_no_type") return true;
    if (parent == "SELF_TYPE") return child == "SELF_TYPE";
    if (child == "SELF_TYPE") return is_subtype(current_class, parent, current_class, class_table);

    string curr = child;
    while (curr != "Object") {
        if (curr == parent) return true;
        if (!class_table.count(curr)) return false;
        curr = class_table.at(curr).parent_name;
    }
    return parent == "Object";
}

string find_type(const string& name, const vector<pair<string, string>>& scope, const string& class_name, const ClassTable& class_table) {
    for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
        if (it->first == name) return it->second;
    }
    string current = class_name;
    while (true) {
        if (class_table.count(current)) {
            if (class_table.at(current).attributes.count(name)) {
                return class_table.at(current).attributes.at(name).type;
            }
            if (class_table.at(current).parent_name.empty()) break;
            current = class_table.at(current).parent_name;
        } else break;
    }
    return "";
}

string least_upper_bound(string type1, string type2, const string& class_name, const ClassTable& class_table) {
    if (type1 == "_no_type" || type2 == "_no_type") return "_no_type";
    if (type1 == type2) return type1;
    string t1 = (type1 == "SELF_TYPE") ? class_name : type1;
    string t2 = (type2 == "SELF_TYPE") ? class_name : type2;

    vector<string> path1;
    string p1 = t1;
    while (p1 != "Object" && class_table.count(p1)) {
        path1.push_back(p1);
        p1 = class_table.at(p1).parent_name;
    }
    path1.push_back("Object");

    string p2 = t2;
    while (p2 != "Object" && class_table.count(p2)) {
        for (const auto& p : path1) {
            if (p == p2) return p2;
        }
        p2 = class_table.at(p2).parent_name;
    }
    return "Object";
}

string check_expressions(CoolParser::ExprContext* expr, const string& class_name, const ClassTable& class_table, vector<pair<string, string>> scope, vector<string>& errors) {
    if (!expr) return "Object";

    if (expr->LET()) {
        for (auto* vardecl : expr->vardecl()) {
            string name = vardecl->OBJECTID()->getText();
            string type = vardecl->TYPEID()->getText();
            if (vardecl->expr()) {
                string init_type = check_expressions(vardecl->expr(), class_name, class_table, scope, errors);
                if (init_type != "_no_type") {
                    if (!is_subtype(init_type, type, class_name, class_table)) errors.push_back("Initializer for variable `" + name + "` in let-in expression is of type `" + init_type + "` which is not a subtype of the declared type `" + type + "`");
                }
            }
            scope.push_back({name, type});
        }
        if (!expr->expr().empty()) {
            return check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        }
        return "Object";
    }

    if (expr->CASE()) {
        check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        string lub_type = "";
        size_t branch_count = expr->TYPEID().size();
        set<string> used_types;
        for (size_t i = 0; i < branch_count; ++i) {
            string var_name = expr->OBJECTID(i)->getText();
            string type_name = expr->TYPEID(i)->getText();
            
            if (type_name == "SELF_TYPE") errors.push_back("`" + var_name + "` in case-of-esac declared to be of type `SELF_TYPE` which is not allowed");
            if (type_name != "SELF_TYPE" && !class_table.count(type_name)) errors.push_back("Option `" + var_name + "` in case-of-esac declared to have unknown type `" + type_name + "`");
            if (used_types.count(type_name)) errors.push_back("Multiple options match on type `" + type_name + "`");
            
            used_types.insert(type_name);
            vector<pair<string, string>> branch_scope = scope;
            branch_scope.push_back({var_name, type_name});
            string branch_type = "Object";
            if (i + 1 < expr->expr().size()) branch_type = check_expressions(expr->expr(i+1), class_name, class_table, branch_scope, errors);
            
            lub_type = lub_type.empty() ? branch_type : least_upper_bound(lub_type, branch_type, class_name, class_table);
        }
        return lub_type;
    }

    if (expr->ASSIGN()) {
        string name = expr->OBJECTID(0)->getText();
        string type = find_type(name, scope, class_name, class_table);
        if (type.empty()) errors.push_back("Assignee named `" + name + "` not in scope");
        
        string rhs_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        if (!type.empty() && rhs_type != "_no_type" && !is_subtype(rhs_type, type, class_name, class_table)) {
            errors.push_back("In class `" + class_name + "` assignee `" + name + "`: `" + rhs_type + "` is not `" + type + "`: type of initialization expression is not a subtype of object type");
        }
        return rhs_type;
    } 
    
    if (expr->DOT()) {
        auto* left_expr = expr->expr(0);
        string left_expr_type = check_expressions(left_expr, class_name, class_table, scope, errors);
        vector<string> arg_types;
        for (size_t i = 1; i < expr->expr().size(); ++i) {
            arg_types.push_back(check_expressions(expr->expr(i), class_name, class_table, scope, errors));
        }

        string dispatch_type = (left_expr_type == "SELF_TYPE") ? class_name : left_expr_type;
        string method_name = expr->OBJECTID(0)->getText();
        
        if (expr->AT()) {
            string static_type = expr->TYPEID(0)->getText();
            if (static_type != "SELF_TYPE" && !class_table.count(static_type)) {
                errors.push_back("Undefined type `" + static_type + "` in static method dispatch");
                return "_no_type";
            }
            if (!is_subtype(left_expr_type, static_type, class_name, class_table)) errors.push_back("`" + left_expr_type + "` is not a subtype of `" + static_type + "`");
            dispatch_type = static_type;
        }

        if (dispatch_type == "_no_type") return "_no_type";

        string return_type = "Object";
        bool method_found = false;
        const Method* method = nullptr;
        string current_search_type = dispatch_type;
        while (class_table.count(current_search_type)) {
            const auto& c_node = class_table.at(current_search_type);
            if (c_node.methods.count(method_name)) { 
                method = &c_node.methods.at(method_name);
                return_type = method->return_type;
                method_found = true; 
                break; 
            }
            if (c_node.parent_name.empty()) break;
            current_search_type = c_node.parent_name;
        }
        if (!method_found) {
            if (expr->AT()) errors.push_back("Method `" + method_name + "` not defined for type `" + expr->TYPEID(0)->getText() + "` in static dispatch");
            else errors.push_back("Method `" + method_name + "` not defined for type `" + dispatch_type + "` in dynamic dispatch");
            return "_no_type";
        }

        size_t provided_args = expr->expr().size() - 1;
        size_t expected_args = method->formals.size();
        if (provided_args != expected_args) {
            errors.push_back("Method `" + method_name + "` of type `" + dispatch_type + "` called with the wrong number of arguments; " + to_string(expected_args) + " arguments expected, but " + to_string(provided_args) + " provided");
            return "_no_type";
        }

        for (size_t i = 0; i < provided_args; ++i) {
            string arg_type = arg_types[i];
            string formal_type = method->formals[i].type;
            if (!is_subtype(arg_type, formal_type, class_name, class_table)) {
                errors.push_back("Invalid call to method `" + method_name + "` from class `" + dispatch_type + "`:");
                errors.push_back("  `" + arg_type + "` is not a subtype of `" + formal_type + "`: argument at position " + to_string(i) + " (0-indexed) has the wrong type");
            }
        }

        if (return_type == "SELF_TYPE") return left_expr_type;
        return return_type;
    } 
    
    if (expr->OBJECTID().size() == 1 && !expr->OPAREN() && !expr->NEW()) {
        string name = expr->OBJECTID(0)->getText();
        if (name != "self") {
            string type = find_type(name, scope, class_name, class_table);
            if (type.empty()) {
                errors.push_back("Variable named `" + name + "` not in scope");
                return "_no_type";
            }
            return type;
        }
        return "SELF_TYPE";
    }

    if (expr->IF()) {
        string cond_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        if (cond_type != "Bool" && cond_type != "_no_type") errors.push_back("Type `" + cond_type + "` of if-then-else-fi condition is not `Bool`");
        
        string t1 = check_expressions(expr->expr(1), class_name, class_table, scope, errors);
        string t2 = check_expressions(expr->expr(2), class_name, class_table, scope, errors);
        return least_upper_bound(t1, t2, class_name, class_table);
    }

    if (expr->WHILE()) {
        string cond_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        if (cond_type != "Bool" && cond_type != "_no_type") errors.push_back("Type `" + cond_type + "` of while-loop-pool condition is not `Bool`");
        check_expressions(expr->expr(1), class_name, class_table, scope, errors);
        return "Object";
    }

    if (expr->OCURLY()) {
        string last_type = "Object";
        for (auto* child : expr->expr()) {
            last_type = check_expressions(child, class_name, class_table, scope, errors);
        }
        return last_type;
    }

    if (expr->INT_CONST()) return "Int";
    if (expr->STR_CONST()) return "String";
    if (expr->BOOL_CONST()) return "Bool";
    if (expr->NEW()) {
        string type_name = expr->TYPEID(0)->getText();
        if (type_name != "SELF_TYPE" && !class_table.count(type_name)) {
            errors.push_back("Attempting to instantiate unknown class `" + type_name + "`");
            return "_no_type";
        }
        return type_name;
    }
    
    if (expr->LT() || expr->LE()) {
        string left_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        string right_type = check_expressions(expr->expr(1), class_name, class_table, scope, errors);
        if (left_type != "Int" && left_type != "_no_type") errors.push_back("Left-hand-side of integer comparison is not of type `Int`, but of type `" + left_type + "`");
        if (right_type != "Int" && right_type != "_no_type") errors.push_back("Right-hand-side of integer comparison is not of type `Int`, but of type `" + right_type + "`");
        return "Bool";
    }

    if (expr->PLUS() || expr->MINUS() || expr->STAR() || expr->SLASH()) {
        string left_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        string right_type = check_expressions(expr->expr(1), class_name, class_table, scope, errors);
        if (left_type != "Int" && left_type != "_no_type") errors.push_back("Left-hand-side of arithmetic expression is not of type `Int`, but of type `" + left_type + "`");
        if (right_type != "Int" && right_type != "_no_type") errors.push_back("Right-hand-side of arithmetic expression is not of type `Int`, but of type `" + right_type + "`");
        return "Int";
    }

    if (expr->TILDE()) {
        string type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        if (type != "Int" && type != "_no_type") errors.push_back("Argument of integer negation is not of type `Int`, but of type `" + type + "`");
        return "Int";
    }

    if (expr->EQ()) {
        string left_type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        string right_type = check_expressions(expr->expr(1), class_name, class_table, scope, errors);
        if (left_type != "_no_type" && right_type != "_no_type") {
            for (const string& type : {"String", "Bool", "Int"}) {
                if (left_type == type && right_type != type) {
                    errors.push_back("A `" + type + "` can only be compared to another `" + type + "` and not to a `" + right_type + "`");
                    break;
                }
                if (right_type == type && left_type != type) {
                    errors.push_back("A `" + type + "` can only be compared to another `" + type + "` and not to a `" + left_type + "`");
                    break;
                }
            }
        }
        return "Bool";
    }

    if (expr->NOT()) {
        string type = check_expressions(expr->expr(0), class_name, class_table, scope, errors);
        if (type != "Bool" && type != "_no_type") errors.push_back("Argument of boolean negation is not of type `Bool`, but of type `" + type + "`");
        return "Bool";
    }

    for (auto* child : expr->expr()) {
        check_expressions(child, class_name, class_table, scope, errors);
    }
    if (expr->ISVOID()) return "Bool";

    return "Object";
}

expected<void *, vector<string>> CoolSemantics::run() {
    vector<string> errors;
    CoolParser::ProgramContext* program = parser_->program();

    vector<CoolParser::ClassContext *> ordered_classes;
    unordered_map<string, CoolParser::ClassContext *> class_map;
    unordered_set<string> basic_classes = {"Object", "IO", "Int", "Bool", "String"};
    for (auto *cls : program->class_()) {
        const string class_name = cls->TYPEID(0)->getText();
        if (class_map.count(class_name)) {
            errors.push_back("Type `" + class_name + "` already defined");
            continue;
        } else if (basic_classes.count(class_name)) {
            errors.push_back("Type `" + class_name + "` already defined");
            continue;
        } else {
            class_map[class_name] = cls;
            ordered_classes.push_back(cls);
        }
    }
    
    unordered_map<string, string> parent_map;
    unordered_set<string> sealed_classes = {"Int", "Bool", "String", "SELF_TYPE"};
    for (auto *cls_context : ordered_classes) {
        const string class_name = cls_context->TYPEID(0)->getText();
        string parent_name = cls_context->INHERITS() ? cls_context->TYPEID(1)->getText() : "Object";
        
        if (sealed_classes.count(parent_name)) {
            errors.push_back("`" + class_name + "` inherits from `" + parent_name + "` which is an error");
        } else if (!basic_classes.count(parent_name) && !class_map.count(parent_name)) {
            errors.push_back(class_name + " inherits from undefined class " + parent_name);
        }
        parent_map[class_name] = parent_name;
    }
    
    vector<vector<string>> loops;
    unordered_set<string> visited;
    for (auto *cls_context : ordered_classes) {
        string curr = cls_context->TYPEID(0)->getText();
        if (visited.count(curr)) continue;

        vector<string> path;
        while (curr != "Object" && parent_map.count(curr)) {
            if (find(path.begin(), path.end(), curr) != path.end()) {
                auto it = find(path.begin(), path.end(), curr);
                loops.push_back(vector<string>(it, path.end()));
                break;
            }
            if (visited.count(curr)) break;

            path.push_back(curr);
            curr = parent_map[curr];
        }
        for (const auto &node : path) visited.insert(node);
    }

    if (!loops.empty()) errors.push_back(print_inheritance_loops_error(loops));
    
    ClassTable class_table;

    class_table["Object"] = {"Object", "", nullptr, {}, {
        {"abort", {"abort", {}, "Object"}},
        {"type_name", {"type_name", {}, "String"}},
        {"copy", {"copy", {}, "SELF_TYPE"}},
    }};
    class_table["IO"] = {"IO", "Object", nullptr, {}, {
        {"out_string", {"out_string", {{"x", "String"}}, "SELF_TYPE"}},
        {"out_int", {"out_int", {{"x", "Int"}}, "SELF_TYPE"}},
        {"in_string", {"in_string", {}, "String"}},
        {"in_int", {"in_int", {}, "Int"}},
    }};
    class_table["Int"] = {"Int", "Object", nullptr, {}, {}};
    class_table["Bool"] = {"Bool", "Object", nullptr, {}, {}};
    class_table["String"] = {"String", "Object", nullptr, {}, {
        {"length", {"length", {}, "Int"}},
        {"concat", {"concat", {{"s", "String"}}, "String"}},
        {"substr", {"substr", {{"i", "Int"}, {"l", "Int"}}, "String"}},
    }};

    for (auto* cls_context : ordered_classes) {
        string class_name = cls_context->TYPEID(0)->getText();
        string parent_name = cls_context->INHERITS() ? cls_context->TYPEID(1)->getText() : "Object";

        ClassNode node = {class_name, parent_name, cls_context, {}, {}};

        for (auto* attr_context : cls_context->attr()) {
            string attr_name = attr_context->OBJECTID()->getText();
            string attr_type = attr_context->TYPEID()->getText();

            if (attr_type != "SELF_TYPE" && !basic_classes.count(attr_type) && !class_map.count(attr_type)) {
                errors.push_back("Attribute `" + attr_name + "` in class `" + class_name + "` declared to have type `" + attr_type + "` which is undefined");
            }

            if (attr_name == "self") errors.push_back("Attribute 'self' is not allowed in class " + class_name + ".");
            if (node.attributes.count(attr_name)) {
                errors.push_back("Attribute `" + attr_name + "` already defined for class `" + class_name + "`");
            } else {
                node.attributes[attr_name] = {attr_name, attr_type};
            }
        }

        for (auto* method_context : cls_context->method()) {
            string method_name = method_context->OBJECTID()->getText();
            if (node.methods.count(method_name)) {
                errors.push_back("Method `" + method_name + "` already defined for class `" + class_name + "`");
                continue;
            }
            Method method = {method_name, {}, method_context->TYPEID()->getText()};
            const string& return_type = method.return_type;
            if (return_type != "SELF_TYPE" && !basic_classes.count(return_type) && !class_map.count(return_type)) {
                errors.push_back("Method `" + method_name + "` in class `" + class_name + "` declared to have return type `" + return_type + "` which is undefined");
            } else {
                set<string> formal_names;
                for (auto* formal_context : method_context->formal()) {
                    string formal_name = formal_context->OBJECTID()->getText();
                    string formal_type = formal_context->TYPEID()->getText();

                    if (formal_type == "SELF_TYPE") errors.push_back("Formal argument `" + formal_name + "` declared of type `SELF_TYPE` which is not allowed");
                    if (formal_type != "SELF_TYPE" && !basic_classes.count(formal_type) && !class_map.count(formal_type)) {
                        errors.push_back("Method `" + method_name + "` in class `" + class_name + "` declared to have an argument of type `" + formal_type + "` which is undefined");
                    }

                    if (formal_name == "self") errors.push_back("Formal parameter 'self' is not allowed in method " + method_name + ".");
                    if (formal_names.count(formal_name)) errors.push_back("Formal parameter " + formal_name + " is multiply defined in method " + method_name + ".");
                    
                    formal_names.insert(formal_name);
                    method.formals.push_back({formal_name, formal_type});
                }
            }
            node.methods[method_name] = method;
        }
        class_table[class_name] = node;
    }

    for (auto* cls_context : ordered_classes) {
        string class_name = cls_context->TYPEID(0)->getText();
        string parent_name = class_table.at(class_name).parent_name;

        for (auto* attr_context : cls_context->attr()) {
            if (attr_context->expr()) {
                auto* init_expr = attr_context->expr();
                string init_expr_type = check_expressions(init_expr, class_name, class_table, {}, errors);
                string attr_name = attr_context->OBJECTID()->getText();
                string attr_type = attr_context->TYPEID()->getText();

                if (init_expr_type != "_no_type" && !is_subtype(init_expr_type, attr_type, class_name, class_table)) {
                    errors.push_back("In class `" + class_name + "` attribute `" + attr_name + "`: `" + init_expr_type + "` is not `" + attr_type + "`: type of initialization expression is not a subtype of declared type");
                }
            }
        }

        for (auto* method_context : cls_context->method()) {
            vector<pair<string, string>> scope;
            for (auto& formal : class_table.at(class_name).methods.at(method_context->OBJECTID()->getText()).formals) {
                scope.push_back({formal.name, formal.type});
            }
            string body_type = check_expressions(method_context->expr(), class_name, class_table, scope, errors);
            string return_type = class_table.at(class_name).methods.at(method_context->OBJECTID()->getText()).return_type;
            
            if (!is_subtype(body_type, return_type, class_name, class_table)) {
                errors.push_back("In class `" + class_name + "` method `" + method_context->OBJECTID()->getText() + "`: `" + body_type + "` is not `" + return_type + "`: type of method body is not a subtype of return type");
            }
        }

        for (auto const& [attr_name, attr] : class_table.at(class_name).attributes) {
            string current_parent = parent_name;
            while (!current_parent.empty()) {
                if (class_table.count(current_parent) && class_table.at(current_parent).attributes.count(attr_name)) {
                    errors.push_back("Attribute `" + attr_name + "` in class `" + class_name + "` redefines attribute with the same name in ancestor `" + current_parent + "` (earliest ancestor that defines this attribute)");
                    break;
                }
                if (!class_table.count(current_parent)) break;
                current_parent = class_table.at(current_parent).parent_name;
            }
        }

        for (auto const& [method_name, method] : class_table.at(class_name).methods) {
            string current_parent = parent_name;
            while (!current_parent.empty()) {
                if (class_table.count(current_parent) && class_table.at(current_parent).methods.count(method_name)) {
                    const Method& parent_method = class_table.at(current_parent).methods.at(method_name);
                    bool signature_mismatch = method.return_type != parent_method.return_type || method.formals.size() != parent_method.formals.size();
                    if (!signature_mismatch) {
                        for (size_t i = 0; i < method.formals.size(); ++i) {
                            if (method.formals[i].type != parent_method.formals[i].type) {
                                signature_mismatch = true;
                                break;
                            }
                        }
                    }
                    if (signature_mismatch) errors.push_back("Override for method " + method_name + " in class " + class_name + " has different signature than method in ancestor " + current_parent + " (earliest ancestor that mismatches)");
                    break;
                }
                if (!class_table.count(current_parent)) break;
                current_parent = class_table.at(current_parent).parent_name;
            }
        }
    }
    
    dynamic_cast<CommonTokenStream *>(parser_->getTokenStream())->seek(0);
    
    for (const auto &error : TypeChecker().check(parser_)) {
        errors.push_back(error);
    }

    if (!errors.empty()) return unexpected(errors);
    
    return nullptr;
}
