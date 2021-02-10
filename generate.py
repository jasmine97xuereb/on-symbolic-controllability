from sys import argv
import math

try:
  nb_choice = int(argv[1])
except:  
  print("Enter Number of Repetition: ") 
  nb_choice = int(input())

string1= "l(x).(if x==4 then k<x>.2 else k<x>.1)"
# string2 = "rec X.(k<1>.(l<1>.X)+(q<1>.1))"
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

# print(string1)

# ------------------------- generating M_rec -----------------------------------

# for i in range(nb_choice-1):
#     string2 = string2 + "+ (k<" + str(i+2) + ">.(l<" +str(i+2)+ ">.X)+(q<" +str(i+2)+ ">.1))"

# string2 = string2 + "+(k<"+ str(nb_choice+1) +">.(l<" +str(nb_choice+1)+ ">.X)+(q<" +str(nb_choice+1)+ ">.1))"    

# print(string2)




for i in range(nb_choice-1):
    string2 = string2 + "+ (k<" + str(i+2) +">.k<(y*" + str(i+2) + ")>.(l<(y*" +str(i+2)+ ")>.X)+(q<(y*" +str(i+2)+ ")>.1))"

string2 = string2 + "+(k<" + str(nb_choice+1) +">.k<(y*"+ str(nb_choice+1) +")>.(l<(y*" +str(nb_choice+1)+ ")>.X)+(q<(y*" +str(nb_choice+1)+ ")>.1))"    

# print(string2)


# ------------------------- generating M_brc -----------------------------------

inner_t = ""
for i in range(nb_choice*4):
  inner_t = inner_t + "(k<" + str(i) + ">.1)+"
inner_t = inner_t + "(k<" + str(nb_choice*4) + ">.1)"

inner_f = ""
for i in range(nb_choice*4):
  inner_f = inner_f + "(k<" + str(i) + ">.2)+"
inner_f = inner_f + "(k<" + str(nb_choice*4) + ">.2)"

# if nb_choice == 1:
#   string3 = "l(x).if x==4 then k<x>." + inner_t + " else k<x>." + inner_f
# else:
string3 = "l(x).(if x==4 then k<x>." + inner_t + " else k<x>." + inner_f + ")"
for i in range(nb_choice):
  temp = "if x mod 2 == 0 then "
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
