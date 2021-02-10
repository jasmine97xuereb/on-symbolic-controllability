from sys import argv
import math

try:
  nb_choice = int(argv[1])
except:  
  print("Enter Number of Repetition: ") 
  nb_choice = int(input())

string1= "l(x).(if x==4 then k<x>.2 else k<x>.1)"
string2 = "rec X.l(x).l(y).if (x>0)&(x<100)&(x==y) then k<x>.k<y>.2 else k<x>.(k<1>.(l<(1*y)>.X)+(q<(1*y)>.1))"
string3 = ""

# ------------------------- FIRST MONITOR TEMPLATE -----------------------------

# ------------------------- generating M_cnd -----------------------------------

if nb_choice == 1:
  string1 = "l(x).if x==4 then k<x>.2 else k<x>.1"
else:
  for i in range(nb_choice-1):
    temp = "if x mod 2 == 0 then "
    counter = 6+(2*(i)) 
    for x in range(i+1):
        temp = temp + "if x<" + str(counter) + " then " 
        counter -= 2
    temp = temp + "if x>2 then k<x>.2 else k<x>.1"
    for x in range(i+1):
        temp = temp + " else k<x>.1"
    temp = temp+" else k<x>.1"
    string1 = string1 + " + ("+temp+")"

print(string1)

# ------------------------- generating M_rec -----------------------------------

for i in range(nb_choice-1):
    string2 = string2 + "+ (k<" + str(i+2) +">.k<(y*" + str(i+2) + ")>.(l<(y*" +str(i+2)+ ")>.X)+(q<(y*" +str(i+2)+ ")>.1))"

string2 = string2 + "+(k<" + str(nb_choice+1) +">.k<(y*"+ str(nb_choice+1) +")>.(l<(y*" +str(nb_choice+1)+ ")>.X)+(q<(y*" +str(nb_choice+1)+ ")>.1))"    

print(string2)


# ------------------------- generating M_brc -----------------------------------

inner_t = ""
for i in range(nb_choice*3):
  inner_t = inner_t + "(k<" + str(i) + ">.1)+"
inner_t = inner_t + "(k<" + str(nb_choice*3) + ">.1)"

inner_f = ""
for i in range(nb_choice*3):
  inner_f = inner_f + "(k<" + str(i) + ">.2)+"
inner_f = inner_f + "(k<" + str(nb_choice*3) + ">.2)"

if nb_choice == 1:
  string3 = "l(x).if x==4 then k<x>." + inner_t + " else k<x>." + inner_f
else:
  string3 = "l(x).(if x==4 then k<x>." + inner_t + " else k<x>." + inner_f + ")"
  for i in range(nb_choice-1):
    temp = "if x mod 2 == 0 then "
    counter = 6+(2*(i)) 
    for x in range(i+1):
        temp = temp + "if x<" + str(counter) + " then " 
        counter -= 2
    temp = temp + "if x>2 then k<x>." + inner_t + " else k<x>." + inner_f
    for x in range(i+1):
        temp = temp + " else k<x>." + inner_f
    temp = temp+" else k<x>." + inner_f
    string3 = string3 + " + ("+temp+")"

# print(string3)


# --------------- M_inf -------------------------

temp1 = ""
temp2 = ""
cond = ""
for i in range(2,nb_choice+2):
  temp2 = "(k<(y*" + str(i) + ")>.X) +" + temp2
inner_s = temp2 
inner_s = inner_s[:-1]

if nb_choice == 1:
  string4 = "l(x).rec X.l(y).(if !(y==x) then k<1>.1 else k<(y*2)>.X) + (if x == y then k<(y*2)>.X  else k<1>.1)"
else: 
  temp = ""
  for i in range(1,nb_choice):
    temp = "if x < (y*" + str(i*3) + ") then " + temp
  temp += "if x == y then "+ inner_s + " else k<1>.1"
  for i in range(1,nb_choice):
    temp = temp + " else k<1>.1"
  string4 = "l(x).rec X.l(y).(if !(y==x) then k<1>.1 else " +  inner_s + ") + (" + temp + ")" 

# print(string4)


# ------------------------- SECOND MONITOR TEMPLATE -----------------------------

# ------------------------- generating M_fail -----------------------------------
# one cont and one not

b1 = ""
inner_t = ""
for i in range(nb_choice*3):
  b1 = b1 + "(k<" + str(i) + ">.1)+"
  inner_t = inner_t + "(k<" + str(i) + ">.0)+"
b1 = b1 + "(k<" + str(nb_choice*3) + ">.1)"
inner_t = inner_t + "(k<" + str(nb_choice*3) + ">.0)"

inner_f = ""
b2 = ""
for i in range(nb_choice*3):
  b2 = b2 + "(k<" + str(i) + ">.2)+"
  inner_f = inner_f + "(k<" + str(i) + ">.0)+"
inner_f = inner_f + "(k<" + str(nb_choice*3) + ">.0)"
b2 = b2 + "(k<" + str(nb_choice*3) + ">.2)"

if nb_choice == 1:
  string3 = "l(x).l<x>.if x==4 then k<x>." + b1 + " else k<x>." + b2
else:
  string3 = "l(x).(l<x>.if x==4 then k<x>." + b1 + " else k<x>." + b2 + ")"
  for i in range(nb_choice-1):
    temp = "l<x>.if x mod 2 == 0 then "
    temp2 = "(recX.k<1>.X)"
    counter = 6+(2*(i)) 
    for x in range(i+1):
        temp = temp + "if x<" + str(counter) + " then " 
        counter -= 2
    temp = temp + "if x>2 then k<x>." + inner_t + " else k<x>." + inner_f
    for x in range(i+1):
        temp = temp + " else k<x>." + inner_f
    temp = temp+" else k<x>." + inner_f
    string3 = string3 + " + ("+temp+")"

print(string3)

# -------------------------- M_rch --------------------------

inner_t = "k<y>.1"
inner_f = ""
for i in range(nb_choice*3):
  inner_f = inner_f + "(k<" + str(i) + ">.X)+"
inner_f = inner_f + "(k<" + str(nb_choice*3) + ">.X)"

if nb_choice == 1:
  string3 = "rec X.l(x).let y = ((2*x)+1) in if y mod 2 == 0 then k<x>." + inner_t + " else k<x>." + inner_f
else:
  string3 = "rec X.l(x).let y = ((2*x)+1) in (if y mod 2 == 0 then k<x>." + inner_t + " else k<x>." + inner_f + ")"
  for i in range(nb_choice-1):
    temp = "if y mod 2 == 0 then k<x>.k<y>.1 else k<x>."
    for x in range(i*3):
        temp = temp + "if !(x==" + str((2*x)+1) + ") then k<x>." 
    temp = temp + inner_f 
    for x in range(i*3):
        temp = temp + " else k<x>." + inner_f
    
    string3 = string3 + " + ("+temp+")"

print(string3)





