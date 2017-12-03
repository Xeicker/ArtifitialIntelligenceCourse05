# -*- coding: UTF-8 -*-
def Valor(D):
	return D[0]/float(len(D))
def Libres(T):
	l = []
	for i in range(9):
		if T[i]==" ":
			l.append(i)
	return l
def T_to_C(T):
	return "".join(T)
def G(x,Tc):
	if Tc[::4]==3*x or Tc[2:7:2]==3*x:
		return True
	for i in range(3):
		if Tc[i*3:i*3+3] == x*3 or Tc[i::3] == x*3:
			return True
	return False
def Max(Tc):
	l = Libres(Tc)
	if l==[]:
		return [0]
	else:
		for i in l:
			Taux = Tc[:i] + "x" + Tc[i+1:]
			if(G("x",Taux)):
				return [1,i]
		p=[]
		for i in l:
			Taux = Tc[:i] + "x" + Tc[i+1:]
			p.append(Min(Taux)+[i])
		return max(p , key = Valor)
def Min(Tc):
	l = Libres(Tc)
	if l==[]:
		return [0]
	else:
		for i in l:
			Taux = Tc[:i] + "o" + Tc[i+1:]
			if(G("o",Taux)):
				return [-1,i]
		p=[]
		for i in l:
			Taux = Tc[:i] + "o" + Tc[i+1:]
			p.append(Max(Taux)+[i])
		return min(p , key = Valor)
def Update_T(T,v,x,y):
	Tablero[y] = Tablero[y][:x] + v + Tablero[y][x+1:] 
def Imprimir_T(T):
	print "\n"+"\n_____\n".join(["|".join(Tablero[y]) + "\t" + "|".join(["[" + str(x) +"," +str(y) +"]" for x in range(3)]) for y in range(len(Tablero))])+"\n"
Tablero = ["   ","   ","   "]
j = raw_input("Desea jugar con x? [s/n]")
j = j=="s"
if j:
	Imprimir_T(Tablero)
while Libres(T_to_C(Tablero)):
	if not j:
		m1 =Max(T_to_C(Tablero))
		m = m1[-1]
		Update_T(Tablero,"x",m%3,m/3)
		Imprimir_T(Tablero)
		if G("x",T_to_C(Tablero)):
			print "Perdiste :("
			exit()
		elif(len(Libres(T_to_C(Tablero)))==0):
			print "Empate -_-"
			exit()
		continuar = False
		while  not continuar:
			x,y = map(int,raw_input().split(","))
			continuar = x+y*3 in Libres(T_to_C(Tablero))
			if not continuar:
				print "Ingrese una solucion válida"
		Update_T(Tablero,"o",x,y)
		if G("o",T_to_C(Tablero)):
			Imprimir_T(Tablero)
			print "Ganaste! :D"
			exit()
	else:
		continuar = False
		while  not continuar:
			x,y = map(int,raw_input().split(","))
			continuar = x+y*3 in Libres(T_to_C(Tablero))
			if not continuar:
				print "Ingrese una solucion válida"
		Update_T(Tablero,"x",x,y)
		if G("x",T_to_C(Tablero)):
			Imprimir_T(Tablero)
			print "Ganaste! :D"
			exit()
		elif(len(Libres(T_to_C(Tablero)))==0):
			Imprimir_T(Tablero)
			print "Empate -_-"
			exit()
		m1 =Min(T_to_C(Tablero))
		m = m1[-1]
		Update_T(Tablero,"o",m%3,m/3)
		if G("o",T_to_C(Tablero)):
			Imprimir_T(Tablero)
			print "Perdiste :("
			exit()
		Imprimir_T(Tablero)

#rint Min(T_to_C(["   ","   ","   "]))
