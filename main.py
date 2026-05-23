from itertools import combinations
from sympy import Poly, symbols, GF, nextprime, ZZ, roots
import math
# Poly - базовый класс многочлена, symbols - переменные,
# GF - конечные поля Галуа, nextprime - генерация простых чисел,
# ZZ - кольцо целых чисел, roots - быстрый поиск рациональных корней.

# Утилита для красивого форматирования вывода.
def format_poly(poly_expr):
    s = str(poly_expr).replace('**', '^')
    return f"({s})"

# Вычисление симметричного остатка, переход из диапазона [0, m-1] в диапазон [-m/2, m/2]
# для восстановления отрицательных коэффициентов.
def symmetric_mod(coeff, m):
    r = int(coeff) % m
    return r if r <= m // 2 else r - m

# Вычисление границы Ландау-Миньотта, это теоретичсекая верхняя граница для абсолютных значений коэффициентов
# любого нетревиального делителя многочлена f(x) в кольце Z[x]. Знание этой границы позволяет нам выбрать
#достаточно большую степень k для модуля p^k в Гензелевском подъеме, чтобы гарантированно восстановить целые числа.
def get_mignotte_bound(f):
    n = f.degree()
    norm = math.sqrt(sum(c ** 2 for c in f.all_coeffs()))
    return int(2 ** n * abs(int(f.LC())) * norm)

#Алгоритм Гензелевского подъема поднимает разложение F_target = g1*h1(mod p) до разложения (mod p^k)
# Важно чтобы F_target, g1 и h1 были приведенными (со старшим коэффициентом 1)
#или корректно отмасштабированными по модулю.
def hensel_lift(F_target, g1, h1, p, k):
    x = F_target.gen

    #Шаг 1: Инициализация
    # Переводим множители в конечное поле GF(p)
    g_p = Poly(g1, domain=GF(p))
    h_p = Poly(h1, domain=GF(p))

    # Применяем расширенный алгоритм Евклида.
    # Находим полиномы a(x) и b(x) такие, что выполняется соотношение Безу:
    # a(x)*g_p(x) + b(x)*h_p(x) = 1 (mod p)
    a_p, b_p, _ = g_p.gcdex(h_p)

    # Создаем рабочие копии поднимаемых многочленов в кольце Z
    g_lift = Poly(g1, domain=ZZ)
    h_lift = Poly(h1, domain=ZZ)

    # p_pow будет хранить текущую степень p
    p_pow = p

    #Шаг 2: Основной цикл подъема
    #Поднимаем точность от p^2 до p^k (итеративно).
    for i in range(2, k + 1):
        # Вычисляем ошибку на текущем шаге:
        # F_target(x) - g(x)h(x) гарантированно делится на p^(i-1)
        diff = F_target - g_lift * h_lift

        # Делим разницу на p^(i-1) и берем по модулю p, получая полином c(x)
        c_coeffs = [(c // p_pow) % p for c in diff.all_coeffs()]
        c_p = Poly(c_coeffs, x, domain=GF(p))

        # Ищем поправки a' и b' для обновления g и h.
        # Нам нужно решить уравнение: g*a' + h*b' = c (mod p)
        # Умножаем b_p на c_p и делим на g_p (с остатком), чтобы степень b' была меньше степени g
        q, b_prime = (c_p * b_p).div(g_p)
        a_prime = (c_p * a_p) + q * h_p

        # Обновляем многочлены, добавляя поправки, умноженные на p^(i-1):
        # g_new = g_old + p^(i-1) * b'
        # h_new = h_old + p^(i-1) * a'
        g_lift = g_lift + Poly([c * p_pow for c in b_prime.all_coeffs()], x, domain=ZZ)
        h_lift = h_lift + Poly([c * p_pow for c in a_prime.all_coeffs()], x, domain=ZZ)

        # Переходим к следующей степени простого числа для следующей итерации
        p_pow *= p
    return g_lift, h_lift

# Объединение алгоритмов Берлекампа и Гензелевского подъема и проверка множителей на истинность
def factorization_final(poly_list):
    x = symbols('x')
    #Этап 1: Очистка от тривиальных нулевых корней
    # Если свободный член равен нулю, выносим 'x' за скобки и рекурсивно вызываем функцию
    if len(poly_list) > 1 and poly_list[-1] == 0:
        return [x] + factorization_final(poly_list[:-1])
    try:
        f = Poly(poly_list, x, domain=ZZ)
    except:
        return [poly_list]

    # Базовый случай: многочлены степени 0 или 1 неприводимы по определению
    if f.degree() <= 1:
        return [f.as_expr()]

    #Этап 2: Поиск рациональных корней
    # Быстрая проверка на наличие линейных множителей вида (x - c).
    f_roots = roots(f)
    if f_roots:
        root = list(f_roots.keys())[0]
        if root.is_integer:
            # Если корень целый, производим полиномиальное деление, в q записываем частое в _ остаток
            q, _ = f.div(Poly(x - root, x, domain=ZZ))
            # Возвращаем линейный множитель и рекурсивно факторизуем частное
            return [x - root] + factorization_final(q.all_coeffs())

    #Этап 3: Подготовка к алгоритму Берлекампа
    bound = get_mignotte_bound(f)
    p = 2  # Начинаем поиск подходящего простого числа с 2

    # Ищем простое число p, которое не портит свойства многочлена
    while p < bound + 1000:
        p = nextprime(p)
        # Условие 1: p не должно делить старший коэффициент (чтобы степень не упала)
        if int(f.LC()) % p == 0: continue
        # Переводим многочлен в поле GF(p)
        f_p = Poly(f, domain=GF(p))
        # Условие 2: Многочлен не должен иметь кратных корней в GF(p).
        # Проверяется через НОД(f, f') == 1
        if not f_p.gcd(f_p.diff()).is_one: continue

        #Алгоритм Берлекампа
        # SymPy выполняет факторизацию над конечным полем
        factors_p = [fact.set_domain(ZZ) for fact, mult in f_p.factor_list()[1]]

        # Если в поле GF(p) многочлен неприводим, делаем выводы:
        if len(factors_p) <= 1:
            # Если p больше границы Миньотта — многочлен абсолютно неприводим в Z[x]
            if p > bound: break
            # Иначе это может быть неудачное (исключительное) p, берем следующее
            continue

        #Гензелевский подъем
        # Вычисляем нужную степень k, чтобы p^k превышало удвоенную границу Миньота
        k = math.ceil(math.log(2 * bound + 1, p))
        big_m = p ** k  # Наш новый модуль для кольца вычетов

        # Трюк со старшим коэффициентом (LC-trick):
        # Чтобы алгоритм Гензеля работал корректно для неприведенных многочленов,
        # мы "делаем" его приведенным (monic) по модулю big_m, умножая на модульную инверсию LC.
        lc_inv = pow(int(f.LC()), -1, big_m)
        F_target = Poly([(c * lc_inv) % big_m for c in f.all_coeffs()], x, domain=ZZ)
        lifted_factors = []
        current_F = F_target
        # Многофакторный подъем: отщепляем по одному множителю за раз.
        # Поскольку функция hensel_lift работает только с двумя полиномами,
        # мы группируем множители как g и h (где h — произведение всех остальных).
        for i in range(len(factors_p) - 1):
            g = factors_p[i]
            h = Poly(1, x, domain=ZZ)
            # Перемножаем оставшиеся множители по модулю p
            for fact in factors_p[i + 1:]:
                h = Poly([(c) % p for c in (h * fact).all_coeffs()], x, domain=ZZ)
            # Поднимаем пару (g, h)
            g_lift, h_lift = hensel_lift(current_F, g, h, p, k)
            lifted_factors.append(g_lift)  # Сохраняем поднятый множитель
            current_F = h_lift  # Оставшаяся "хвостовая" часть становится новой целью для подъема
        # Последний оставшийся блок также является поднятым множителем
        lifted_factors.append(current_F)
        #Этап 4: Комбинаторика
        indices = list(range(len(lifted_factors)))
# Длина комбинации r идет до половины общего числа множителей
        for r in range(1, (len(indices) // 2) + 1):
            for combo in combinations(indices, r):
                # Начинаем собирать потенциальный делитель
                # Добавляем старший коэффициент исходного многочлена
                g_test = Poly([f.LC()], x, domain=ZZ)
                # Перемножаем факторы из текущей комбинации
                for idx in combo:
                    g_test = (g_test * lifted_factors[idx]).set_domain(ZZ)
                # Восстанавливаем отрицательные коэффициенты (переход из [0, M) в [-M/2, M/2])
                res_coeffs = [symmetric_mod(c, big_m) for c in g_test.all_coeffs()]
                # Функция primitive() возвращает кортеж (содержание, примитивная_часть).
                # Индекс [1] берет примитивную часть, удаляя общий числовой множитель (наш добавленный LC).
                candidate = Poly(res_coeffs, x, domain=ZZ).primitive()[1]
                #Конечная проверка
                # Если кандидат имеет валидную степень, проверяем, делит ли он исходный многочлен нацело
                if 0 < candidate.degree() < f.degree():
                    q, rem = f.div(candidate)
                    if rem.is_zero:  # Если остаток равен нулю — мы нашли настоящий множитель в Z[x]!
                        # Возвращаем кандидата и продолжаем рекурсивно раскладывать оставшуюся часть q
                        return [candidate.as_expr()] + factorization_final(q.all_coeffs())
        # Если перебор завершился, а делителей нет, и p > bound
        if p > bound: break
    # Если мы дошли до сюда, многочлен абсолютно неприводим в кольце целых чисел
    return [f.as_expr()]

user_line = input("Введите коэффициенты через пробел (от старшей степени к младшей): ")
if user_line.strip():
  user_coeffs = [int(val) for val in user_line.split()]
  final_factors = factorization_final(user_coeffs)
  result_output = " * ".join([format_poly(f) for f in final_factors])
  print(f"\nИтоговое разложение:")
  print(result_output)
  print("\nУспешное завершение работы алгоритма")