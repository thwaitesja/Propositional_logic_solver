# Justin Thwaites
# Final Project
# Or | +
# And & *
# XOR ^
# IMPLIES -> $ =>
# BIDIRECTIONAL <-> - = == <=> _


from z3 import *

class LogicSolver:
    def  __init__(self, mystring = ""):
        self.mySolver = Solver()
        self.myString = []
        self.myVars = {}
        self.lastModel = []
        if mystring:
            self.add_string(mystring)

    def add_string(self, mystring):
        #allows the user to add a string to the equation
        mystring = mystring.upper().replace(" ", "") # takes everything as uppercase and strips spaces
        self.myString.append(mystring)
        mystring = mystring.replace("==", "-").replace("=", "-").replace("<->", "_").replace("->", "$").replace("-", "_").replace("!", "~").replace("+", "|").replace("*", "&")
        setup = [letter for letter in mystring]
        self.myVars = {**self.myVars, **{letter: Bool(letter) for letter in setup if letter not in ["~", "&", "^", "|", "(", ")", "$", "_"]}}
        # dictionary of all bool variables
        self.mySolver.add(self.Solverify(self.Listify(setup)))



        return  self.mySolver

    def Solverify(self, mylist):
        #converts the listified values in my list to an actual z3 expression
        options = {"$": lambda x, y: Implies(x,y), "_": lambda x, y: Not(Xor(x,y)),"&": lambda x, y: And(x,y), "^": lambda x, y: Xor(x,y), "|": lambda x, y: Or(x,y), "~": lambda x: Not(x)}
        if len(mylist)== 1:
            return self.myVars[mylist[0]]
        elif len(mylist)== 2:
            return options[mylist[0]](self.Solverify(mylist[1]))
        elif len(mylist)== 3:
            return options[mylist[0]](self.Solverify(mylist[1]), self.Solverify(mylist[2]))
        else:
            print("Incorrect Input to Solverify")

    def __str__(self):
        # defines how the object is printed out
        if len(self.myString) == 1:
            return f"{self.myString[0]} is {self.mySolver.check()}isfiable"
        else:
            return f"{self.myString} together are {self.mySolver.check()}isfiable"

    def Listify(self, setup):
        # returns format [&, a, [~, b]] in a recursive fashion for an entire string
        count = 0
        for character in setup:
            if character == "(":
                count +=1
            elif character == ")":
                count -=1
        if count:
            raise ArgumentError("Parentheses do not match")
        while len(setup) > 1:  # format [&, a, [~, b]]
            new_setup = []
            flag = False
            setupline = setup.copy()
            pbalance = False
            for i, element in enumerate(setup):

                if element == "~":
                    # print("~")
                    if setupline[0] == "~" and setupline[1] != "(":
                        new_setup.append(["~", setupline[1]])
                        del setupline[0:2]
                        flag = True
                    elif setupline[0] == "~":
                        new_setup.append("~")
                        del setupline[0]
                    elif setupline[1] == "~":
                        new_setup.append("&")
                        new_setup.append(setupline[1])
                        del setupline[0:2]
                    else:
                        raise SyntaxError("Malformed Input")
                elif element in ["_","$","^","|","&"] :
                    if setupline[0] == element:
                        new_setup.append(element)
                        del setupline[0]
                    elif setupline[1] == element and (setup[i + 1] == "(" or setup[i + 1] == "~" or setup[i - 1] == ")"):
                        new_setup.append(element)
                        del setupline[0:2]
                    elif setupline[1] == element and i > 1 and setup[i - 2] in ["_","$","^","|","&"]:
                        new_setup.append(element)
                        del setupline[0:2]
                    elif setupline[1] == element:
                        del new_setup[-1]
                        new_setup.append([element, setupline[0], setupline[2]])
                        del setupline[0:3]
                        flag = True
                    else:
                        raise SyntaxError("Malformed Input")

                elif element == "(":
                    # print("(")
                    if setupline[0] == "(" and setupline[2] == ")":
                        del setupline[0]
                        del setupline[1]
                        pbalance = True
                    elif setupline[0] == "(":
                        new_setup.append(setupline[0])
                        del setupline[0]
                    elif setupline[1] == "(":
                        new_setup.append("&")
                        new_setup.append(setupline[1])
                        del setupline[0:2]
                    else:
                        raise SyntaxError("Malformed Input")
                elif element == ")":
                    # print(")")
                    if not pbalance:
                        if setupline[0] == ")":
                            new_setup.append(")")
                            del setupline[0]
                        elif setupline[1] == ")":
                            new_setup.append(")")
                            del setupline[0:2]
                        else:
                            raise SyntaxError("Malformed Input")
                    else:
                        pbalance = False
                else:
                    # print("*")
                    if not flag:
                        new_setup.append(element)
                    else:
                        flag = False

                # print(setupline)

            # print(" ")
            setup = new_setup
        return setup[0]

    def returnSolver(self):
        #returns the z3 solver for any other future use
        return self.mySolver

    def block_model(self, flag = True):
        #blocks the boolean expressions
        if flag:
            mym = self.mySolver.model()
            mym = str(mym).strip("[]").replace("\n", "").split(", ")
            # print(mym)
            mym = {var[0]: var for var in mym}

            if not self.lastModel or len(mym) == len(self.myVars):
                self.lastModel = mym
            elif len(mym) != len(self.myVars):
                for var in mym:
                    self.lastModel[var] = mym[var]
        trues = [ Not(self.myVars[v[0]]) for i, v in enumerate(self.lastModel) if "True" in self.lastModel[v]]
        falses = [ self.myVars[v[0]] for i, v in enumerate(self.lastModel) if "False" in self.lastModel[v]]
        return Or(trues + falses)

    def count_model(self):
        #counts the number of possible solutions
        if self.isTautology():
            count = 2**len(self.myVars)
            print(f"There are {count} possible solutions")
            return count
        count = 0
        while self.mySolver.check() == sat:
            count +=1
            self.mySolver.add(self.block_model())
        print(f"There are {count} possible solutions")
        self.Solve_reset()
        return count

    def print_options(self):
        #prints out all possible solutions
        if self.count_model() == 2**len(self.myVars):
            print(f"The Solutions are:")
            mym = ", ".join([f"{var} = True" for var in self.myVars])
            print(mym)
            mym = str(mym).strip("[]").split(", ")
            mym = {var[0]: var for var in mym}
            self.lastModel = mym
            self.mySolver.add(self.block_model(False))
        else:
            print(f"The Solutions are:")
        while self.mySolver.check() == sat:
            self.mySolver.add(self.block_model())
            print(str([self.lastModel[x] for x in self.lastModel]).strip("[]").replace("\'", ""))
        self.Solve_reset()

    def Solve_reset(self):
        #internally used function to reset the solver after performing some calculations
        self.mySolver = Solver()
        strings = self.myString
        self.myString = []
        self.myVars = {}
        for string in strings:
            self.add_string(string)

    def isTautology(self):
        # generates an inverted solver and sees if it is satisfiable
        tempSolver = LogicSolver()
        tempSolver.add_string(f"~("+("&".join(self.myString))+")")
        if tempSolver.returnSolver().check() == unsat:
            return True
        return False

    def variable_specs(self, variables):
        # Prints out if a variable must be true false or can be either
        if len(variables) == 0:
            variables = self.myVars
        if len(variables) > 1:
            for var in variables:
                self.variable_specs(var)
        else:
            choice = 0
            variables = variables.upper()
            self.mySolver.add(self.myVars[variables])
            if self.mySolver.check() == unsat:
                choice += 1
            self.Solve_reset()
            self.mySolver.add(Not(self.myVars[variables]))
            if self.mySolver.check() == unsat:
                choice += 2
            self.Solve_reset()
            variable_option = {0:"can be either True or False", 1: "must be False", 2: "must be True", 3: "--- Error it can't be Either"}
            print(f"{variables} {variable_option[choice]} for the equations to be satisfied")




# Example use HW 4
# """On the island of knights and knaves, you preside over the trial of two
# inhabitants, V and W, accused of a crime. At the opening of the proceedings, it is
# not known whether V and W are both innocent, both guilty, or one innocent and the
# other guilty.
# Eight islanders, A, B, C, D, E, F, G, and H, are heard as witnesses. They make the
# following statements:
# • A says, “I am a knight.”
# • B remains silent.
# • C says, “A is a knave.”
# • D says, “B is a knave.”
# • E says, “C and D are both knights.”
# • F says, “A and B are not both knaves.”
# • G says, “E and F are either both knights or both knaves.”
# • H says, “G and I are either both knights or both knaves, and V and W are not
# both guilty.”
# """
# #
p4 = LogicSolver()
p4.add_string("a<->a")
p4.add_string("c<->~A")# Captialization independent
p4.add_string("D<->!b")# ! is the same as ~
p4.add_string("e<->(c&d)")# parentheses can be use for greater clarification of order
p4.add_string(" f <- > (a|b)")# spaces do not have any effect on the expression
p4.add_string("g<-> ~(e^f)")# inclues special characters such as ^
p4.add_string("h<-> ((g <-> h)& ~(v & w))")# V and w stand fo if v and w are guilty or not
p4.mySolver.check()
p4.count_model()
p4.print_options()
p4.variable_specs("vw")
#
#
# #Uncomment below for the recursive setup demo of Listify
# print(p4.Listify([letter for letter in "h|((g^h)&~(v&w))"]))
#
# #A) example of Tautology
# a = LogicSolver("A|~A|B")
# print(a)
# print(a.isTautology())
# a.count_model()
# a.print_options()
#
# #B) example of generic use
# b = LogicSolver("A-> (B&C)")
# print(b)
# print(b.isTautology())
# b.print_options()
#
# b.add_string("A&~B")
# print(b)
