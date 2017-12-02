# -*- coding: UTF-8 -*-
import random
import string
def  CorrectForm(s):
	if(s[:3]=="⊻"):
		s=s[3:]
	if(s[-3:]=="⊻"):
		s=s[:-3]
	s = s.replace("⊻⊻","⊻")
	return s
def Update(s):
	values = s.values()
	keys = s.keys()
	for i in range(len(values)):
		if values[i] in s:
			s[keys[i]]=s[values[i]]
def IsVariable(x):
	if x[0].isupper():
		return False
	return x.isalnum()
def IsConstant(x):
	if x[0].islower():
		return False
	return x.isalnum()
def IsPredicateOrFunction(x):
	if x[0]=="[":
		return False
	return "(" in x
def Args(x):
	return "["+x[x.find("(")+1:-1]+"]"
def Operator(x):
	return "".join(x.split("(")[:1])
def  Res(x):
	return "["+",".join(x.split(",")[1:])
def  First(x):
	return "".join(",".join(x.split(",")[0:1])[1:].split("]"))
def  CountArgs(x):
	return len(x.split(","))
def  Unify_var(x,y,s):
	if x in s:
		return Unify(s[x],y,s)
	elif y in s:
		return Unify(x,s[y],s)
	elif IsPredicateOrFunction(y) and (x in y):
		return "fail"
	else:
		s[x]=y
		return s
def Unify(x,y,s={}):

	if s=="fail":
		return "fail"
	elif x==y:
		Update(s)
		return s
	elif ("=" in x) and ("=" in y):
		xs = x.split("=")
		ys = y.split("=")
		if len(xs)!= len(ys):
			return "fail"
		for i in range(len(xs)):
			res = Unify(xs[i],ys[i],s)
			if res == "fail":
				return "fail"
			else:
			 s = dict(s,**res)
		Update(s)
		return s
	elif (("=" in x) and ("=" not in y)) or (("=" not in x) and ("=" in y)):
		return "fail"
	elif IsVariable(x):
		return Unify_var(x,y,s);
	elif IsVariable(y):
		return Unify_var(y,x,s);
	elif IsPredicateOrFunction(x) or IsPredicateOrFunction(y):
		if Operator(x)==Operator(y):
			return Unify(Args(x),Args(y),s)
		else:
			return "fail"
	elif IsConstant(x) and IsConstant(y):
		return "fail"
	else:
		if CountArgs(x)==CountArgs(y):
			return Unify(Res(x),Res(y),Unify(First(x),First(y),s))
		else:
			return "fail"
def Skolemize(exp):
	exp1 = exp.split("∃")
	if (len(exp1[0])==0):
		Const = []
		exp2 = exp1[-1][1:]
		for i in range(1,len(exp1)):
			s = random.choice(string.ascii_lowercase)
			while s in exp or s in Const:
				s+=random.choice(string.ascii_lowercase)
			Const.append(s)
			exp2 = exp2.replace(exp1[i][0],s)
		return exp2
	pt_Vars = exp1[0].split("∀")[1:]
	Const = []
	exp2 = exp1[-1][1:]
	for i in range(1,len(exp1)):
		s = random.choice(string.ascii_lowercase)
		while s in exp or s in Const:
			s+=random.choice(string.ascii_lowercase)
		Const.append(s)
		exp2 = exp2.replace(exp1[i][0],s+"("+",".join(map(str,pt_Vars))+")")
	return exp2
def Resolution(exp1,exp2):
	neg = lambda s: s[:2] == "¬"
	pos = lambda s: s[:2] != "¬"
	exps1 = exp1.split("⊻")
	exps2 = exp2.split("⊻")
	exps1 = [filter(neg,exps1),filter(pos,exps1)]
	exps2 = [filter(neg,exps2),filter(pos,exps2)]
	for neg in exps1[0]:
		for pos in exps2[1]:
			res = Unify(neg[2:],pos,{})
			if res!="fail":
				sol = CorrectForm(exp1.replace(neg,"") + exp2.replace(pos,""))
				for keys in res:
						sol = sol.replace(keys,res[keys])
				return [sol,res]
	for neg in exps2[0]:
		for pos in exps1[1]:
			res = Unify(neg[2:],pos,{})
			if res!="fail":
				sol = CorrectForm(exp2.replace(neg,"")  + exp1.replace(pos,""))
				for keys in res:
						sol = sol.replace(keys,res[keys])
				return [sol,res]	
	return "fail"
def Modulation(expEq,expOr):
	validEq = lambda eq: "=" in eq and not "¬" in eq
	Eq = expEq.split("⊻")
	Or = expOr.replace("=","⊻").split("⊻")
	for i in range(len(Eq)):
		if validEq(Eq[i]):
			Eqi = Eq[i].split("=")
			for j in range(len(Or)):
				for k in range(2):
					if Or[j][:2]!="¬":
						res = Unify(Eqi[k],Or[j],{})
						if res!= "fail":
							Eq.pop(i)
							exp = "⊻".join(Eq) +"⊻"+ expOr.replace(Or[j],Eqi[(k+1)&1])
							for keys in res:
								exp = exp.replace(keys,res[keys])
							return [CorrectForm(exp),res]
	return "fail"
def Size_Of_Exp(exp):
	return len(exp.replace("=","⊻").split("⊻"))
def Verify_Contradiction(exps):
	for i in range(len(exps)):
		if exps[i][:2]=="¬":
			for j in range(len(exps)):
				if exps[i][2:] == exps[j]:
					return True
	return False
def Reduccion_Absurdo(exps,question):
	k=0
	res = True
	#exps.sort(key=Size_Of_Exp)
	for i in range(len(exps)):
		res = Resolution(exps[i],question)
		if  res != "fail":
			exps.append(res[0])
			if(Verify_Contradiction(exps)):
				return "Comprobado"
		res = Modulation(exps[i],question)
		if  res != "fail":
			exps.append(res[0])
			if(Verify_Contradiction(exps)):
				return "Comprobado"
	exps.append(question)
	while k<100:
		exps.sort(key=Size_Of_Exp)
		sizes = [Size_Of_Exp(exp) for exp in exps]
		aux= len(exps)

		x = 0
		y = 1
		cambio = False
		while y<aux-1:
			res = Resolution(exps[x],exps[y])
			if  res != "fail":
				if res[0] not in exps:
					print "Resolution(" + exps[x] + "," + exps[y] + ") \t\t " + res[0]
					cambio=True
					exps.append(CorrectForm(res[0]))
				if Verify_Contradiction(exps):
					print "\n".join(map(str,exps))
					return "Comprobado"
			res = Modulation(exps[x],exps[y])
			if  res != "fail":
				if res[0] not in exps:
					print "Modulation(" + exps[x] + "," + exps[y] + ") \t\t\t\t " + res[0]
					cambio=True
					exps.append(CorrectForm(res[0]))
				if Verify_Contradiction(exps):
					print "\n".join(map(str,exps))
					return "Comprobado"
			if cambio:
				break
			x+=1
			if x>=len(exps):
				y+=1
				x=0
		k+=1
	print "\n".join(map(str,exps))
	return "No se sabe"
#print ",".join(map(str,Modulation("K⊻z⊻¬T(c)=v(c,V)","j(N)⊻v(M,x)")))
exps=[	"M(x)=Fo⊻M(x)=B",\
		"W(x,M(x))",\
		"¬T(x)⊻¬M(x)=B",\
		"F(I)",\
		"T(I)",\
	]
q = "¬W(I,Fo)"
#print Unify("Cocodrilo(foca,Caballo)=tres","Cocodrilo(mono,serpiente)=dos")
#print "1".isalnum()
#print"M(I)=Fo⊻¬M(I)=Fo,M(I)=Fo"
#print "\n".join(map(str,Modulation("¬M(I)=Fo⊻M(I)=Fo","M(I)=Fo")))
print Reduccion_Absurdo(exps,q)
#M(x)=Fo⊻¬T(x)⊻¬M(x)=M(x)
#print Verify_Contradiction(["D(L(J))","¬D(L(J))"])
#print Size_Of_Exp(exps[1])

#print "∀""∃""¬""⊻"
