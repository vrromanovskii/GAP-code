# GAP-code
Программа позволяет вычислять гомологии свободной нильпотентной алгебры Ли. Ниже представлено описание программы.

Для начала опишем функцию, которая по слову $w$ выдаёт стандартное разложение $w=uv$, если $w$ является словом Линдона. Назовём эту функцию StandardDecomposition. Построим вспомогательные функции ListOfSuffixes и IsLyndonWord. Функция \\  ListOfSuffixes по всякому слову l выдаёт набор всех собственных суффиксов слова l. Функция IsLyndonWord проверяет, является ли слово l словом Линдона, сравнивая его со всеми элементами ListOfSuffixes(l), т.е. со всеми собственными суффиксами слова l. Если l меньше всех своих суффиксов, то l объявляется словом Линдона и IsLyndonWord(l)$:="\text{true}"$, иначе IsLyndonWord(l)$:="\text{false}"$. Теперь без труда строим StandardDecomposition(w). Сначала проверяем, верно ли, что \\ IsLyndonWord(w)=$\text{true}$. Если это верно, то задаём \\ $v=\text{minimum}(\text{ListOfSuffixes}(w))$, а в качестве $u$ берём оставшийся префикс. 

Функция lyn\_comm(l) -- скобка Линдона, построена рекурсивно. Если $l$ -- слово Линдона единичной длины, то lyn\_comm(l):=l, иначе берём коммутатор скобок Линдона от $u$ и $v$, где $l=uv$ -- стандартное разложение слова Линдона.

Функция LyndonShirhovBasis(p) -- разложение некоммутативного многочлена $p(a,b) \in L(a,b)$ по базису Ширшова-Линдона, устроена так: берём некоммутативный многочлен $p$, выбираем в нём минимальный моном $w$, затем вычитаем из $p$ скобку Линдона $[w]$ минимального монома с подходящим коэффициентом и получаем либо нулевой многочлен, либо многочлен, слагаемые которого увеличились, однако остались прежних длин. Поскольку длина слагаемых не меняется, за конечное число повторений данной операции получим нулевой многочлен. Так получаем разложение некоммутативного многочлена $p$ по базису  Ширшова-Линдона $\{ [w] | w \in {\sf Lyn}_{\leq N}(X) \}$.


Следующая функция, $\text{Homology}(B,A)$ -  одна из основных функций нашего кода, считает $n$-е гомологии, если $B$ это матрица $n+1$-го дифференциала, а $A$ -- матрица $n$-го дифференциала. Итак, для двух данных матриц $A$ и $B$ функция $\text{Homology}(B,A)$ сначала проверяет, верно ли, что произведение матриц $A$ и $B$ равно нулю, $AB=0$. Затем, если это оказалось верно, выписывает базис ядра $\text{Ker}(A)$. Поскольку $\text{Im}(B) \subseteq \text{Ker}(A)$, то столбцы матрицы B можно разложить по базису $\text{Ker}(A)$. Так сформируем матрицу $B_1$, столбцы которой это столбцы $B$ в базисе $\text{Ker}(A).$ После чего положим $B_2=\text{SmithNormalFormIntegerMat}(B_1)$ -- нормальная форма Смита матрицы $B_1$. Заметим, что $B_1$ матрица отображения из $\mathbb{Z}^k=\text{Ker}A$ в $\mathbb{Z}^m$, как и матрица $B_2$. Заметим, что $B_2$ диагональная и несёт в себе всю информацию о гомологиях, поскольку, если $(a_1, a_2, \ldots , a_{min\{k,m\}})$ главная диагональ матрицы $B_2$, то $\text{Ker}(A)/\text{Im}(B)=\mathbb{Z}^k/\text{Im}(B_2) \cong \mathbb{Z}/a_1 \oplus \mathbb{Z}/a_2 \oplus \ldots \mathbb{Z}/a_{min\{k,m\}}.$ 


Функция LyndonWordsLengthN(N) выдаёт список слов Линдона длины N, состоящих из двух букв. Строится индуктивно, для слов единичной длины это набор $[[1],[2]]=[[a],[b]]$, дальше для всех $i$ от единицы до $k-1$ собирается список слов Линдона длины $k$ из двух списков слов Линдона длины $i$ и $k-i$ путём конкатенации (если  $u$ и $v$ слова Линдона и $u<v$, то $uv$ тоже слово Линдона).


Аналогично строятся функции LyndonWordsLengthNon3letters(N) и \\ LyndonWordsLengthNon4letters(N), формирующие списки слов Линдона длины N на трёх и четырёх буквах.

Функция LyndonWordsLengthLessOrEqualN(N) формирует список слов Линдона длины не больше N на двух буквах.

Функция BasisOfExteriorPower(n, N) выводит базис n-ой внешней степени кольца Ли на множестве $\{a,b\}$ ступени нильпотентности N. 

Функция Differential(l, N) вычисляет значение дифференциала $$\partial_n(x_1\wedge \ldots \wedge x_n)=\sum_{1\leqslant i<j \leqslant n}(-1)^{i+j-1}[x_i,x_j]\wedge x_1\wedge \ldots \wedge \hat{x}_i \ldots \wedge \hat{x}_j \ldots \wedge x_n.$$ на базисном элементе для ступени нильпотентности N.

Функция MatrixOfDiff(n,N) строит матрицу $n$-го дифференциала для ступени нильпотентности N стандартным образом: берём базис n-ой внешней степени и базис $n-1$-ой внешней степени, вычисляем значение дифференциала на k-ом базисном элементе $n$-ой внешней степени, записываем коэффициенты этого значения в базисе $n-1$-ой внешней степени в $k$-ый столбец матрицы.
