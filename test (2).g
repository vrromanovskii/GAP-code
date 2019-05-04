#Read("test.g");

LoadPackage("EDIM");
LoadPackage("GaussForHomalg");
LoadPackage("GBNP");
GBNP.ConfigPrint("x","y");
#ll:= [];;



ListOfSuffixes:=function(l_) #  лист суффиксов
local n,l,i,ll;
l:=ShallowCopy(l_);
n:=Length(l);
ll:=[];
for i in [1..n-1] do # вычёркиваем первый элемент и добавляем в список
	Remove(l,1);;
	Add(ll,ShallowCopy(l));
od;
return ll;
end;



IsLyndonWord:= function(l)  #проверка на линдоновость
if l < Minimum(ListOfSuffixes(l)) then #если слово меньше минимального суффикса, то это слово Линдона
return true;
else
return false;
fi;
end;



StandardDecomposition:= function(l) #стандартное разложение
local l1,l2,k;
l2:=Minimum(ListOfSuffixes(l)); #минимальный суффикс		
k:=Length(l)-Length(l2);
l1:=l{[1..k]}; #оставшийся преффикс
if IsLyndonWord(l) then
return [l1,l2];
else
return "error";
fi;
end;


NoncommutativePolynomial:= function(l) #неккомутативный многочлен по листу
return ([[l],[1]]);
end;


commutator:= function(p1_, p2_)#коммутатор двух многочленов
local p1,p2,p;
p1:=ShallowCopy(p1_);
p2:=ShallowCopy(p2_);
p:=AddNP(MulNP(p1,p2),MulNP(p2,p1),1,-1);
return p;
end;




lyn_comm:= function(l_) #скобка Линдона
local n,l;
l:=ShallowCopy(l_);
n:=Length(l);
if n=1 then
return np(l);
else 
return commutator(lyn_comm(StandardDecomposition(l)[1]),lyn_comm(StandardDecomposition(l)[2]));
fi;
end;


MinimalMonomial:= function(p) #минимальный моном многочлена
local k,a;
k:= Position(p[1], Minimum(p[1]));
a:= p[2][k];
return [[Minimum(p[1])],[a]];
end;



1LyndonShirshovBasis:= function(p_,ll_) #шаг разложения по базису Ширшова-Линдона
local p,ll;
p:=ShallowCopy(p_);
ll:=ShallowCopy(ll_);
if p=[[],[]] then
return [p,ll];
else
Add(ll, MinimalMonomial(p));
p:= AddNP(p, lyn_comm(MinimalMonomial(p)[1][1]), 1, -MinimalMonomial(p)[2][1]);
return [p,ll];
fi;
end;

LyndonShirshovBasis:= function(p_) #разложение некоммутативного многочлена по базису Ширшова-Линдона
local p, ll;
p:=ShallowCopy(p_);
ll:=[];
while p<>[[],[]] do
Add(ll, MinimalMonomial(p));
p:= AddNP(p, lyn_comm(MinimalMonomial(p)[1][1]), 1, -MinimalMonomial(p)[2][1]);
od;
return ll;
end;

LyndonShirshovBasisCommutator:= function(l1_,l2_) #разложение коммутатора по базису
local l1, l2, p1, p2;
l1:= ShallowCopy(l1_);
l2:= ShallowCopy(l2_);
p1:= lyn_comm(l1);
p2:= lyn_comm(l2);
return LyndonShirshovBasis(commutator(p1,p2));
end;


#ChangeRows:= function(M_,i_,k_) #меняю местами строки
#local M,i,k;
#M:= ShallowCopy(M_);
#i:= ShallowCopy(i_);
#k:= ShallowCopy(k_);
#M[i]:= M_[k];
#M[k]:= M_[i];
#return M;
#end;


#ChangeColumns:= function(M_,i_,k_) #меняю местами столбцы
#local M,i,k;
#M:= ShallowCopy(M_);
#i:= ShallowCopy(i_);
#k:= ShallowCopy(k_);
#M:= TransposedMat(ChangeRows(TransposedMat(M),i,k));
#return M;
#end;


#MultRowByConst:= function(M_,i_,c_) #умножаю строку на константу
#local M,i,c;
#M:= ShallowCopy(M_);
#i:= ShallowCopy(i_);
#c:= ShallowCopy(c_);
#M[i]:=c*M[i];
#return M;
#end;


#MultColByConst:= function(M_,k_,c_) #умножаю столбец на константу
#local M,k,c;
#M:= ShallowCopy(M_);
#k:= ShallowCopy(k_);
#c:= ShallowCopy(c_);
#M:= TransposedMat(MultRowByConst(TransposedMat(M),k,c));
#return M;
#end;


#AddRowMultByConst:= function(M_,i1_,i2_,c_) #прибавляю к строке i1 #строку i2, умноженную на константу
#local M,i1,i2,c;
#M:= ShallowCopy(M_);
#c:= ShallowCopy(c_);
#i1:= ShallowCopy(i1_);
#i2:= ShallowCopy(i2_);
#M[i1]:=M[i1]+c*M[i2];
#return M;
#end;


#AddColMultByConst:= function(M_,k1_,k2_,c_) #прибавляю к столбцу k1 #столбец k2, умноженный на константу
#local M,k1,k2,c;
#M:= ShallowCopy(M_);
#c:= ShallowCopy(c_);
#k1:= ShallowCopy(k1_);
#k2:= ShallowCopy(k2_);
#M:= TransposedMat(AddRowMultByConst(TransposedMat(M),k1,k2,c));
#return M;
#end;


#FirstNonzeroOfMatrix:= function(M_) #первый ненулевой элемент матрицы
#local M,i,j;
#M:= ShallowCopy(M_);
#i:= PositionNonZero(M);
#if i<=Length(M) then
#j:= PositionNonZero(M[i]);
#return [i,j];
#else
#return "нулевая матрица";
#fi;
#end;






#SNF1:= function(m_) # 1 шаг по строкам для нормальной формы Смитта
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#m:= ChangeRows(m,FirstNonzeroOfMatrix(m)[1],1);
#m:= ChangeColumns(m,FirstNonzeroOfMatrix(m)[2],1);
#z:= PositionProperty(m[1], n -> n mod AbsInt(m[1][1])<>0);
#	if z in [1 .. Length(m[1])] then
#	l:= QuotientRemainder(m[1][z], m[1][1]);
#	m:= AddColMultByConst(m,z,1,-l[1]);
#	m:=ChangeColumns(m,1,z);
#	fi;
#return m;
#fi;
#end;


#SNF2:= function(m_) # 2 шаг по строкам для нормальной формы Смитта #(строка -> делящаяся строка)
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#repeat
#m:=SNF1(m);
#until IsZero(m[1]{[2..Length(m[1])]} mod m[1][1]);
#return m;
#fi;
#end;


#SNF3:= function(m_) # 3 шаг по строкам для нормальной формы Смитта
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m[1]{[2..Length(m[1])]}) then
#return m;
#else
#l:= EuclideanQuotient(m[1][PositionNonZero(m[1]{[2..Length(m[1])]})+1], #m[1][1]);
#m:= AddColMultByConst(m,PositionNonZero(m[1]{[2..Length(m[1])]})+1,1,-#l);
#return m;
#fi;
#end;

#SNF4:= function(m_) # 4 шаг (строка -> справа нули)
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#repeat
#m:=SNF3(m);
#until IsZero(m[1]{[2..Length(m[1])]});
#return m;
#fi;
#end;


#SNF2_:= function(m_) # столбец -> делящийся столбец
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#m:=TransposedMat(m);
#repeat
#m:=SNF1(m);
#until IsZero(m[1]{[2..Length(m[1])]} mod m[1][1]);
#m:=TransposedMat(m);
#return m;
#fi;
#end;


#SNF4_:= function(m_) # столбец -> снизу нули
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#m:=TransposedMat(m);
#repeat
#m:=SNF3(m);
#until IsZero(m[1]{[2..Length(m[1])]});
#m:=TransposedMat(m);
#return m;
#fi;
#end;




#SNFBase0:= function(m_) # первая часть базового шага
#local m,l,z;
#m:= ShallowCopy(m_);
#if IsZero(m) then
#return m;
#else
#repeat
#m:= SNF4_(SNF2_(SNF4(SNF2(m))));
#until IsZero(m[1]{[2..Length(m[1])]});
#return m;
#fi;
#end;


#SNFBase1:= function(m_) # корректировка базового шага
#local m,z;
#m:= ShallowCopy(m_);
#if IsZero(m mod m[1][1]) then
#return m;
#else
#repeat
#z:= PositionProperty(m, n -> n mod AbsInt(m[1]#[1])<>ListWithIdenticalEntries(Length(m[1]),0)); #номер первой строки с элементом, не делящимся на m[1][1]
#m:= AddRowMultByConst(m,1,z,1);
#m:= SNFBase0(m);
#until IsZero(m mod m[1][1]);
#return m;
#fi;
#end;


#SNFBase:= function(m_) #базовый шаг
#local m;
#m:= ShallowCopy(m_);
#m:= SNFBase1(SNFBase0(m));
#return m;
#end;


#SubM:= function(m_) #вычеркиваю первый столбец и первую строку
#local m;
#m:= ShallowCopy(m_);
#if Length(m[1])=1 then
#return m;
#elif Length(m)=1 then
#return m;
#else
#m:= m{[2..Length(m)]}{[2..Length(m[1])]};
#return m;
#fi;
#end;


#SNF:= function(m_) #нормальная форма Смитта
#local m,m1;
#m:= List(m_, ShallowCopy);
#m:= SNFBase(m);
#if SubM(m)=m then
#return m;
#else
#m1:= SubM(m);
#m{[2..Length(m)]}{[2..Length(m[1])]}:= SNFBase(m1);
#return m;
#fi;
#end;# не могу сделать шаг. Оказалось, в gap есть встроенная функция.



Homology:= function(B_,A_)#считает гомологии
local B,A,B1,i,V,O,ll,B2,a,b,j;
B:=ShallowCopy(B_);#на всякий случай всегда пишу ShallowCopy
A:=ShallowCopy(A_);
if IsZero(A*B) then 
	if IsZero(NullspaceMat(TransposedMat(A))) then 
	return "гомологии нулевые"; #если ядро А нулевое, то гомологии нулевые (беру транспонированную матрицу, потому что GAP умножает справа вектор на матрицу, а я слева)
	else
V:= VectorSpace( Rationals, NullspaceMat(TransposedMat(A))); #V - векторное пространство над Q, базис которого - базис ядра А
O:= Basis(V, NullspaceMat(TransposedMat(A))); #зафиксировали базис V
B1:= ListWithIdenticalEntries(Length(TransposedMat(B)),0);
for i in [1..Length(TransposedMat(B))] do
B1[i]:= Coefficients( O, TransposedMat(B)[i]);
od; #B1 - матрица, строки которой это столбцы матрицы B, переписанные в базисе ядра А
#Print(TransposedMat(B1));
ll:=[];
B2:=SmithNormalFormIntegerMat(TransposedMat(B1));# Нормальная форма Смита матрицы, транспонированной к B1
#Print(B2);
#if IsZero(B2) then #если B2 нулевая матрица, то выводим нулевой список длины главной диагонали матрицы B2 
#ll:=ListWithIdenticalEntries(Length(NullspaceMat(A)),0);
#else
a:=Length(B2[1]);
b:=Length(B2);
for j in [1..Minimum([a,b])] do
Add(ll,B2[j][j]);
od;
#fi;
return ll;#выводим главную диагональ матрицы B2
fi;
else
return "не комплекс";
fi;
end;



#VspomFunct:= function(n_,p_)#вспомогательная функция для проверки делимости
#local n,p,l;
#n:=ShallowCopy(n_);
#p:=ShallowCopy(p_);
#l:= PrimePowersInt(n);
#return l[PositionNthOccurrence(l,p,1)+1];
#end;

#CheckDivisibility:= function(l_,p_)#проверяю делимость
#local l,p,k,i;
#l:= ShallowCopy(l_);
#p:= ShallowCopy(p_);
#Apply(l, i->AbsInt(i));
#Sort(l);
#l:=l{[PositionNonZero(l)..Length(l)]};
#l:=Filtered(l, n -> n mod p = 0 );
#for i in [1..Length(l)] do
#l[i]:=VspomFunct(l[i],p);
#od;
#return l[PositionMaximum(l)];
#end;




ParaPoListam:= function(l1_,l2_)#вспомогательная функция для следующей функции. Берёт два списка слов и формирует по ним новый список, элементы которого -- конкатенации слов из данных двух списков (меньшее слово берём первым)
local l1,l2,ll,i,j;
l1:= ShallowCopy(l1_);
l2:= ShallowCopy(l2_);
ll:=[];
for j in [1..Length(l2)] do
for i in [1..Length(l1)] do
	if l1[i]<l2[j] then
	Add(ll, Concatenation(l1[i],l2[j]));
	elif l2[j]<l1[i] then
	Add(ll, Concatenation(l2[j],l1[i]));
	fi;
	od;
od;
return Unique(ll);
end;



LyndonWordsLengthN:= function(k_)#список слов Линдона длины N из двух букв, строим индуктивно
local k, li, ll,i;
k:= ShallowCopy(k_);
if k=1 then
return [[1],[2]];
else
ll:=[];
for i in [1..k-1] do#берём два списка слов Линдона длины i и k-i и формируем по ним новый список слов Линдона длины k путём конкатенации
Add(ll, ParaPoListam(LyndonWordsLengthN(i),LyndonWordsLengthN(k-i)));
od;
ll:=Concatenation(ll);
return Unique(ll);#исключаем повторяющиеся элементы (оставляем только один, если несколько одинаковых)
fi;
end;

LyndonWordsLengthNon4letters:= function(N_)# список слов Линдона длины N на 4 буквах
local N, li, ll,i,a,b,c,d;
N:= ShallowCopy(N_);
if N=1 then
a:=1;
b:=2;
c:=3;
d:=4;
return [[a],[b],[c],[d]];
else
ll:=[];
for i in [1..N-1] do
Add(ll, ParaPoListam(LyndonWordsLengthNon4letters(i),LyndonWordsLengthNon4letters(N-i)));
od;
ll:=Concatenation(ll);
return Unique(ll);
fi;
end;

LyndonWordsLengthNon3letters:= function(N_)#список слов Линдона длины N на 3 буквах
local N, li, ll, i;
N:=ShallowCopy(N_);
if N=1 then
return [[1],[2],[3]];
else
ll:=[];
for i in [1..N-1] do
Add(ll, ParaPoListam(LyndonWordsLengthNon3letters(i),LyndonWordsLengthNon3letters(N-i)));
od;
ll:=Concatenation(ll);
return Unique(ll);
fi;
end;



LyndonWordsLengthLessOrEqualN:= function(k_)#список слов Линдона на двух буквах длины не больше N
local k,ll,i;
k:= ShallowCopy(k_);
ll:=[];
for i in [1..k] do
Add(ll, LyndonWordsLengthN(i));#формируем список из слов Линдона длины не больше k  
od;
ll:=Concatenation(ll);
return ll;
end;

LyndonWordsLengthLessOrEqualNon4letters:= function(k_)# список слов Линдона на четырёх буквах длины не больше N 
local k,ll,i;
k:= ShallowCopy(k_);
ll:=[];
for i in [1..k] do
Add(ll, LyndonWordsLengthNon4letters(i));
od;
ll:=Concatenation(ll);
return ll;
end;

LyndonWordsLengthLessOrEqualNon3letters:= function(k_)#список слов Линдона на трёх буквах длины не больше N
local k,ll,i;
k:= ShallowCopy(k_);
ll:=[];
for i in [1..k] do
Add(ll, LyndonWordsLengthNon3letters(i));
od;
ll:=Concatenation(ll);
return ll;
end;

BasisOfExteriorPower:= function(n_, N_)#базис n-ой внешней степени, двухбуквенная версия
local n,ll,N;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
ll:= Combinations(LyndonWordsLengthLessOrEqualN(N),n);
Sort(ll);
return Unique(ll);
end;
	
BasisOfExteriorPoweron4letters:= function(n_,N_)#базис n-ой внешней степени четырёхбуквеная версия
local n,ll,N;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
ll:= Combinations(LyndonWordsLengthLessOrEqualNon4letters(N),n);
Sort(ll);
return Unique(ll);
end;


BasisOfExteriorPoweron3letters:= function(n_,N_)#базис n-ой внешней степени трёхбуквеная версия
local n,ll,N;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
ll:= Combinations(LyndonWordsLengthLessOrEqualNon3letters(N),n);
Sort(ll);
return Unique(ll);
end;


BasisOfExteriorPower_k:= function(n_,N_,k_)#базис к-ой n-ой внешней степени (k - это индекс, здесь берём те элементы n-ой внешней степени, суммарная длина слов которых равна k) двухбуквенная версия
local n,N,k,ll,l,i;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
k:= ShallowCopy(k_);
ll:=[];
l:=BasisOfExteriorPower(n,N);
	for i in [1..Length(l)] do
	if Length(Flat(l[i]))=k then
	Add(ll,l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;

BasisOfExteriorPower_kon4letters:= function(n_,N_,k_)#базис к-ой n-ой  внешней степени четырёхбуквенная версия
local n,N,k,ll,l,i;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
k:= ShallowCopy(k_);
ll:=[];
l:=BasisOfExteriorPoweron4letters(n,N);
	for i in [1..Length(l)] do
	if Length(Flat(l[i]))=k then
	Add(ll,l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;


BasisOfExteriorPower_kon3letters:= function(n_,N_,k_)#базис к-ой n-ой внешней степени трёхбуквенная версия
local n,N,k,ll,l,i;
n:= ShallowCopy(n_);
N:= ShallowCopy(N_);
k:= ShallowCopy(k_);
ll:=[];
l:=BasisOfExteriorPoweron3letters(n,N);
	for i in [1..Length(l)] do
	if Length(Flat(l[i]))=k then
	Add(ll,l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;



Reord:= function(l_)#переупорядочивание по возрастанию
local l,l1,i,k;
l1:=ShallowCopy(l_);
k:=l1[1][1];
Sort(l1[1]);
i:=Position(l1[1],k);
l1[2]:=[l1[2][1]*(-1)^(i-1)];
return l1;
end;


Differential:= function(l_,N_)#дифференциал на базисном элементе
local l,l1,ll,i,j,k,l_k,n,N,l2,ii,q,n1,k1,ll_1,j1,ll_j1;#N максимальная длина слов из l (ступень нильпотентности)
l:=ShallowCopy(l_);
ll:=[];
n1:=Length(l);
for i in [1..Length(l)] do
	for j in [1..Length(l)] do
	if i<j then
	l1:=ShallowCopy(l_);
	RemoveSet(l1,l[i]);
	RemoveSet(l1,l[j]);
	if Length(l[i])+Length(l[j])<=N_ then
	for j1 in [1..Length(LyndonShirshovBasisCommutator(l[i],l[j]))] do
	ll_j1:=ShallowCopy(LyndonShirshovBasisCommutator(l[i],l[j]));
	ll_j1[j1][2][1]:=ll_j1[j1][2][1]*((-1)^(i+j));
	Add(ll, [(ll_j1)[j1],l1]);
	od;
	fi;
	fi;
	od;
od;
for k in [1..Length(ll)] do
	l_k:=ll[k];
	#for n in [1..Length(l_k[1])] do
	if Length(l_k[2])>0 then
	for q in [1..Length(l_k[2])] do
	Add(l_k[1][1],l_k[2][q]);
	od;
	fi;
	#od;
	Remove(l_k,2);
	l_k[1][1]:=Unique(l_k[1][1]);
	l_k[1]:=Reord(l_k[1]);
	od;
ll_1:=ShallowCopy(ll);
for k1 in [1..Length(ll)] do
if Length(ll[k1][1][1])<(n1-1) then
Unbind(ll_1[k1]);
fi;
od;
return Compacted(ll_1);
end;


MatrixOfDiff:= function(n_,N_)#Матрица n-го дифференциала для ступени нильпотентности N
local m,l1,l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower(n_,N_);
l2:=BasisOfExteriorPower(n_-1,N_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
#Print(j_i);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;


MatrixOfDiffon4letters:= function(n_,N_)#матрица дифференциала четырёхбуквенная версия
local m,l1,l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPoweron4letters(n_,N_);
l2:=BasisOfExteriorPoweron4letters(n_-1,N_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
#Print(j_i);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;


MatrixOfDiffon3letters:= function(n_,N_)#матрица дифференциала трёхбуквенная версия
local m,l1,l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPoweron3letters(n_,N_);
l2:=BasisOfExteriorPoweron3letters(n_-1,N_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
#Print(j_i);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;


MatrixOfDiff_k:= function(n_,N_,k_)#Матрица дифференциала _k
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_k(n_,N_,k_);
l2:=BasisOfExteriorPower_k(n_-1,N_,k_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;

MatrixOfDiff_kon4letters:= function(n_,N_,k_)#матрица дифференциала _к четырёхбуквенная версия
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kon4letters(n_,N_,k_);
l2:=BasisOfExteriorPower_kon4letters(n_-1,N_,k_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;


MatrixOfDiff_kon3letters:= function(n_,N_,k_)#матрица дифференциала _к трёхбуквенная версия
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kon3letters(n_,N_,k_);
l2:=BasisOfExteriorPower_kon3letters(n_-1,N_,k_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;



BasisOfExteriorPower_kWithNumbOfx:= function(n_,N_,k_,x_)#базис к-ой внешней степени с фиксированным колическтвом иксов
local l,ll,i;
ll:=[];
l:=BasisOfExteriorPower_k(n_,N_,k_);
	for i in [1..Length(l)] do
	if Number(Flat(l[i]),n->n=1)=x_ then
	Add(ll, l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;

BasisOfExteriorPower_kWithNumbOfxon4letters:= function(n_,N_,k_,x_)#базис к-ой внешней степени на четырёх буквах с фиксированным количеством букв "а"
local l,ll,i;
ll:=[];
l:=BasisOfExteriorPower_kon4letters(n_,N_,k_);
	for i in [1..Length(l)] do
	if Number(Flat(l[i]),n->n=1)=x_ then
	Add(ll, l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;


BasisOfExteriorPower_kWithNumbOfxon3letters:= function(n_,N_,k_,x_)#базис к-ой внешней степени на трёх буквах с фиксированным количеством букв "а"
local l,ll,i;
ll:=[];
l:=BasisOfExteriorPower_kon3letters(n_,N_,k_);
	for i in [1..Length(l)] do
	if Number(Flat(l[i]),n->n=1)=x_ then
	Add(ll, l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
return ll;
end;


BasisOfExteriorPower_kWithNumbOfxAndbon3letters:= function(n_,N_,k_,x_,b_)#базис к-ой внешней степени на трёх буквах с фиксированным количеством букв "а", "b"
local l,ll,i,j,k,lll;
ll:=[];
l:=BasisOfExteriorPower_kon3letters(n_,N_,k_);
	for i in [1..Length(l)] do
	if Number(Flat(l[i]),n->n=1)=x_ then
	Add(ll, l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
lll:=[];
	for j in [1..Length(ll)] do
	if Number(Flat(ll[j]),n->n=2)=b_ then
	Add(lll, ll[j]);
	fi;
	od;
if Length(lll)=0 then
Add(lll, ListWithIdenticalEntries(n_,0));
fi;
return lll;
end;

BasisOfExteriorPower_kWithNumbOfxAndbcon4letters:= function(n_,N_,k_,x_,b_,c_)#базис к-ой внешней степени на четырёх буквах с фиксированным количеством букв "a","b" и "с"
local l,ll,i,j,k,lll,llll;
ll:=[];
l:=BasisOfExteriorPower_kon4letters(n_,N_,k_);
	for i in [1..Length(l)] do
	if Number(Flat(l[i]),n->n=1)=x_ then
	Add(ll, l[i]);
	fi;
	od;
if Length(ll)=0 then
Add(ll, ListWithIdenticalEntries(n_,0));
fi;
lll:=[];
	for j in [1..Length(ll)] do
	if Number(Flat(ll[j]),n->n=2)=b_ then
	Add(lll, ll[j]);
	fi;
	od;
if Length(lll)=0 then
Add(lll, ListWithIdenticalEntries(n_,0));
fi;
llll:=[];
	for k in [1..Length(lll)] do
	if Number(Flat(lll[k]),n->n=3)=c_ then
	Add(llll, lll[k]);
	fi;
	od; 
if Length(llll)=0 then
Add(llll, ListWithIdenticalEntries(n_,0));
fi;
return llll;
end;

MatrixOfDiff_kWithNumbOfx:= function(n_,N_,k_,x_)# Матрица дифференциала _к с фиксированным количеством иксов
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kWithNumbOfx(n_,N_,k_,x_);
l2:=BasisOfExteriorPower_kWithNumbOfx(n_-1,N_,k_,x_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;

MatrixOfDiff_kWithNumbOfxon4letters:= function(n_,N_,k_,x_)#Матрица дифференциала _к с фиксированным количеством букв "а" (четырёхбуквенная версия)
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kWithNumbOfxon4letters(n_,N_,k_,x_);
l2:=BasisOfExteriorPower_kWithNumbOfxon4letters(n_-1,N_,k_,x_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;



MatrixOfDiff_kWithNumbOfxon3letters:= function(n_,N_,k_,x_)#Матрица дифференциала _к с фиксированным количеством букв "а" (трёхбуквенная версия)
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kWithNumbOfxon3letters(n_,N_,k_,x_);
l2:=BasisOfExteriorPower_kWithNumbOfxon3letters(n_-1,N_,k_,x_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;



MatrixOfDiff_kWithNumbOfxAndbcon4letters:= function(n_,N_,k_,x_,b_,c_)#Матрица дифференциала _к с фиксированным количеством букв "a", "b", "c".(четырёхбуквенная версия)
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kWithNumbOfxAndbcon4letters(n_,N_,k_,x_,b_,c_);
l2:=BasisOfExteriorPower_kWithNumbOfxAndbcon4letters(n_-1,N_,k_,x_,b_,c_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;


MatrixOfDiff_kWithNumbOfxAndbon3letters:= function(n_,N_,k_,x_,b_)#Матрица дифференциала к_ с фиксированным количеством букв "a", "b"(трёхбуквенная версия)
local m, l1, l2,l_k,k,i,j_i;
l1:=BasisOfExteriorPower_kWithNumbOfxAndbon3letters(n_,N_,k_,x_,b_);
l2:=BasisOfExteriorPower_kWithNumbOfxAndbon3letters(n_-1,N_,k_,x_,b_);
m:=NullMat(Length(l2),Length(l1));
if Length(l1)>0 then
for k in [1..Length(l1)] do
l_k:=Differential(l1[k],N_);
if Length(l_k)>0 then
for i in [1..Length(l_k)] do
j_i:=Position(l2, l_k[i][1][1]);
m[j_i,k]:=l_k[i][1][2][1];
od;
fi;
od;
fi;
return m;
end;




Func2:= function(l_,ll_)
local i,lll,l_i,j,l,ll,k;
l:=ShallowCopy(l_);
ll:=ShallowCopy(ll_);
lll:=[];
for i in [1..Length(ll)] do 
l_i:=Func1(ll[i],5);
for j in [1..Length(l_i)] do
Add(lll, [[l[i]*l_i[j][1][2][1]],l_i[j][1][1]]);
od;
od;
for k in [1..Length(lll)] do
if IsZero(lll[k][1]) then
Unbind(lll[k]);
fi;
od;
return Compacted(lll);
end;


Sokrk_:= function(l_,k_)
local l,i,j,ll,ll1,k,n;
l:=ShallowCopy(l_);
ll:=[];
ll1:=[];
for i in [1..Length(l)] do
	if i<>k_ then
	if l[i][2]=l[k_][2] then
	Add(ll,i);
fi;
fi;
od;
for k in ll do
Add(ll1,l[k][1][1]);
od;
l[k_][1][1]:=l[k_][1][1]+Sum(ll1);
for n in ll do
Unbind(l[n]);
od;
l:=Compacted(l);
#Print([ll,ll1]);
return l;
end;







