import logging
logging.basicConfig(level=logging.WARNING, filename="py_log.log",filemode="w")
from sage.schemes.elliptic_curves.weierstrass_morphism import WeierstrassIso-morphism

def constr_EC(p,q = 2):
    """
    Конструирование кривой + нахождение эндоморфизма
    Вход: p и q(опциально)
    Выход: кривая E, эндоморфизм iota и q
    """
    logging.info("####################")
    logging.info("starting constr_EC()")
    F = GF(p^2)
    if p%4 == 3: 
        E = EllipticCurve(GF(p), [1,0])
        E.set_order(p + 1)
        EE = E.change_ring(F)
        iota,_ = sorted(a for a in EE.automorphisms() if a**4 != a**2)
        return EE, iota, 1,
    
    q = next_prime(q)
    while True:
        if q%4 == 3 and kronecker(-q,p) == -1: break
        else: q = next_prime(q)
    
    # построение многочлена класса Гилберта
    P_K = hilbert_class_polynomial(fundamental_discriminant(-q))
    
    # взятие корня из дискриминанта, чтобы построить кривую
    j = P_K.change_ring(GF(p)).any_root()
    logging.debug(f"q = {q}\nP_K = {P_K}\nj = {j}")

    if q == 3: 
        E = EllipticCurve(GF(p),[0,0,0,0,1])
    else:
        a = 27*j/(4*(1728-j))%p
        E = EllipticCurve(GF(p), [0,0,0,a,a])
    E.set_order(p + 1)
    EE = E.change_ring(F)
    E = E.change_ring(GF(p))
    if 3 <= q <= (p+3)//4:
        iso = WeierstrassIsomorphism(None, (F(-q).sqrt(),0,0,0), EE)
        if q == 3 and EE.a_invariants() == (0,0,0,0,1):
            iota = EE.isogeny(EE(0,1))
        else:
            iota = EE.isogeny(None, iso.domain(), degree=q)
        iota = iso * iota
    logging.debug(f"EE: {EE}\niota: {iota}")
    return E, iota, q

def constr_Max_Order(p,q):
    """
    Конструирование максимального порядка для алгебры кватернионов
    Вход: p, q
    Выход: словарь максимальных порядков {O}
    """
    logging.info("###########################")
    logging.info("starting constr_max_order()")
    B = QuaternionAlgebra(-q,-p)
    logging.debug(f"B: {B}")
    i,j,k = B.gens()
    if p%4 == 3:
        O0 = {
            (i+j)/2: B.quaternion_order([1, i, (i+j)/2, (1+k)/2]),
            }
    elif p%3 == 2:
        O0 = {
            (i+k)/3: B.quaternion_order([1, (1+i)/2, (j+k)/2, (i+k)/3]),
            }
    else:
        c = min(map(ZZ, Mod(-p,q).sqrt(all=True)))
        O0 = {
            (c*i+k)/q: B.quaternion_order([1, (1+i)/2, (j+k)/2, (c*i+k)/q]),
            (c*i-k)/q: B.quaternion_order([1, (1+i)/2, (j+k)/2, (c*i-k)/q])
            }
        logging.debug(f"O0: {O0}")
    return O0

def connecting_Ideal(O0, O1):
    """
    Констрирование связующего идеала между порядками О0 и и О2 
    Вход: максимальные порядки О0 и О1
    Выход: идеал I(O0,O1)
    """
    I = O0*O1
    I = I*I.norm().denominator()
    return I

def equivalent_Prime_Ideal(I, banned = []):
    """
    Построение эквивалентного простого идеала
    Вход: идеал I и список забаненых идеалов
    Выход: нужный идеал I_new
    """    
    logging.info("#################################")
    logging.info("starting equivalent_Prime_Ideal()")    
    
    B = I.quaternion_algebra()
    i,j,k = B.gens()
    p,q = [ZZ(-j**2),ZZ(-i**2)]

    Ibasis = reduced_Basis(I)
    nI = ZZ(I.norm())
    
    m = max(floor(log(p))//10,7)
    logging.debug(f"log(p) = {floor(log(p))},m = {m}")    
    best = (0, +infinity)

    for a1,a2,a3,a4 in linear_Combinations(m):
        delta = a1*Ibasis[0] + a2*Ibasis[1] + a3*Ibasis[2] + a4*Ibasis[3]
        
        dnorm = ZZ(delta.reduced_norm() / nI)
        
        if floor(p**(1/5)) < dnorm < best[1] and dnorm.gcd(2*q)==1 and is_pseudoprime(dnorm) and I*(delta.conjugate()/nI) not in banned:
            best = (delta, dnorm)
            if log(dnorm,2) < (1/1.8)*log(p,2): break
    logging.debug(f"best = {best}")
    return I*(best[0].conjugate()/nI)

def reduced_Basis(I):
    """
    Нахождение редуцированного базиса Минковского
    Вход: идеал I
    Выход: нужный базис в виде списка
    """
    logging.info("########################")
    logging.info("starting reduced_basis()")
    def _matrix_to_gens(M, B):
        return [sum(c * g for c, g in zip(row, B)) for row in M]
    B = I.basis()
    G = I.gram_matrix()
    U = G.LLL_gram().transpose()
    return _matrix_to_gens(U, B)

def linear_Combinations(m):
    """
    Генератор линейной комбинации с коэффицинтами в [-m,m]
    """
    logging.info("##############################")
    logging.info("starting linear_Combinations()")
    for a1 in range(0, m+1):
        for a2 in range(-m, m+1):
            for a3 in range(-m, m+1):
                for a4 in range(-m, m+1):
                    yield (a1, a2, a3, a4)

def represent_Integer(M,O0):
    """
    Нахождение элемента gamma максимального порядка O0, норма которого равна M
    Вход: целое M и максимальный порядок O0
    Выход: gamma 
    """
    logging.info("###########################")
    logging.info("starting RepresentInteger()")
    B = O0.quaternion_algebra()
    i, j, k = B.gens()
    p,q = [ZZ(-j**2),ZZ(-i**2)]
    QF = BinaryQF([1,0,q])
    
    m = max(floor(sqrt(M/((1+q)*p))),3)
    logging.debug(f"m = {m}")
    while True:
        z,t = [randint(-m,m),randint(-m,m)]    
        M_sh = M - p*QF(z,t)
        if M_sh < 0: continue
        sol = QF.solve_integer(M_sh)
        if sol:
            gamma = sol[0]+i*sol[1]+j*(z+i*t)
            return gamma
        
def elem_To_Matrix(a, Mat_1, Mat_i, Mat_j, Mat_k, Fn):
    """
    Перевод элемента a в матричный вид по матричному базису
    Вход: элемент a, базис Mat_1, Mat_i, Mat_j, Mat_k и поле Fn
    Выход: матрица k
    """
    logging.info("#########################")
    logging.info("starting elem_to_matrix()")
    k = sum(Fn(c)*g for c,g in zip(a, (Mat_1,Mat_i,Mat_j,Mat_k)))
    return k

def decomp_Alpha_N(I):
    """
    Нахождение элемента alpha, такого, что I = O*alpha + N*O
    Вход: идеал I
    Выход: элемент a
    """
    logging.info("#######################")
    logging.info("starting DecompAlphaN()")
    N = ZZ(I.norm())
    basis = I.basis()
    while True:
        a = sum([b*randint(0,50) for b in basis])
        if gcd(a.reduced_norm(), N**2) == N: 
            break
    logging.debug(f"alpha = {a}")
    assert I.left_order() * N + I.left_order() * a == I
    return a

def ideal_Mod_Constraint(I, gamma, alpha):
    """
    Дан идеал I = O_0\*alpha + O_0\*N и gamma ∈ O_0, 
    возвращает целые C и D, такие что mu = j*(C+i\*D) 
    удовлетворяет O_0\*gamma\*mu/O_0\*N = I/O_0\*N 
    Вход: идеал I, gamma и alpha
    Выход: С,D
    """
    logging.info("#############################")
    logging.info("starting IdealModConstraint()")
    B = I.quaternion_algebra()
    N = ZZ(I.norm())  
    i, j, k = B.gens()  
    
    p,q = [ZZ(-j**2),ZZ(-i**2)]
    Mat_1 = identity_matrix(GF(N), 2)  
    
    
    Mat_i, Mat_j, Mat_k = B.modp_splitting_data(N) 
    assert Mat_i**2 == -q and Mat_j**2 == -p and Mat_j*Mat_i == -Mat_k  # Про-верка нормирующих условий

    # хотим решить уравнение: gamma * (C * j - D * k) + (a + b * i + c * j + d * k) * alpha == 0
    # Формирование списка элементов уравнения
    # gamma * (j - k) + alpha * (1 + i + j + k)
    els = [gamma * g for g in (j, -k)] + [g * alpha for g in B.basis()]
    logging.debug(f"els = {els}")
    # Преобразование элементов в матрицы
    mats = [elem_To_Matrix(el, Mat_1, Mat_i, Mat_j, Mat_k, GF(N)) for el in els]
    logging.debug(f"mats: \n{mats}")
    # Формирование системы уравнений в виде матрицы
    eqs = matrix(GF(N), zip(*(mat.list() for mat in mats)))
    logging.debug(f"eqs: {eqs}")
    logging.debug(f"{eqs.right_kernel()}")
    # Поиск решения системы уравнений
    for sol in eqs.right_kernel().basis():  
        # Проверка, чтобы первые два элемента и элементы с индекса 4 были ненулевыми
        if sol[:2] and sol[4:]:
            C, D = map(ZZ, sol[:2])
            logging.debug(f"C,D = {C},{D}")
            assert I.left_order() * N + I.left_order() * (gamma * j * (C + i * D)) == I
            return C, D 
        
def strong_Approximation(I,C,D,factT):
    """
    Строгое приближение. 
    Даны простое N и (C_0, D_0) ∈ Z. 
    Находит mu = lambda*mu0 + N*mu1 ∈ O0 с mu0 = j(C_0 + omega*D_0) и mu1 ∈ O0
    Вход: идеал I и (C, D) факторизация T - целевая норма будущего идеала J
    Выход: элемент mu и T - новая целевая норма
    """
    logging.info("##############################")
    logging.info("starting StrongApproximation()")

    B = I.quaternion_algebra()
    i,j,k = B.gens()
    p,q = [-ZZ(j**2),-ZZ(i**2)]
    QF = BinaryQF([1,0,q])
    C,D = [ZZ(C),ZZ(D)]
    N = ZZ(I.norm())

    T = ZZ(prod([l**e for l,e in factT]))
    R = Integers(N)
    logging.debug(f"R(T) = {T}, R(p) = {p},QF = {QF(C,D)}")
    lamsq = R(T) / (R(p) * QF(R(C), R(D)))
    #lamsq = T / (p * QF(C, D))
    logging.debug(f"lamsq = {lamsq}")
    if kronecker(lamsq, N) == -1:
        logging.debug(f"kroneker = {kronecker(lamsq, N) == -1}")
        nonsq = 1
        for pri,e in factT:
            if kronecker(pri, N) == -1:
                logging.debug(f"kroneker2 = {kronecker(pri, N) == -1}")
                nonsq = pri
                break
        else:
            logging.debug("tut")
            return None
        T //= nonsq
        lamsq = R(T) / (R(p) * QF(R(C), R(D)))
    logging.debug(f"new lamsq = {lamsq}")
    lam = ZZ(sqrt(lamsq))
    logging.debug(f"lam = {lam}")

    c_z = 2*lam*p*C
    c_t = 2*lam*p*q*D
    logging.debug(f"c_t = {c_t}, c_z = {c_z}")
    logging.debug(f"T = {T}, QF = {QF(C,D)}")
    logging.debug(f"factor T = {factor(T)}")
    
    c_0 = T - ZZ(p*lam**2*QF(C,D))

    c_t_inv = ZZ(pow(c_t,-1,N))
    
    logging.debug(f"c_0 = {c_0}, c_t_inv = {c_t_inv}")
    logging.debug(f"c_0_term = {c_0.quo_rem(N)}")
    c_0,_ = c_0.quo_rem(N)

    zp0 = 0
    tp0 = ZZ(c_0*c_t_inv % N)

    mat = [[1, ZZ((-c_z*c_t_inv) % N)],
           [0, N]]
    lattice_basis = N * Matrix(ZZ,mat)
    
    target = ZZ(lam)*vector([C, D]) + N*vector([zp0,tp0])
    logging.debug(f"lattice:\n{lattice_basis}")
    logging.debug(f"target = {target}")

    close_vectors = generate_CVP(lattice_basis,target,p,T)

    xp, yp = None, None
    for close in close_vectors:
        zp, tp = close
        zp = ZZ(zp/N) + zp0
        tp = ZZ(tp/N) + tp0
        
        M = T - p * QF(lam * C + zp * N, lam * D + tp * N)
        M,_ = M.quo_rem(N**2)
        assert _ == 0, "должно быть целым"
        if M < 0: continue
        
        try:
            sol = QF.solve_integer(ZZ(M))
        except TypeError:
            continue
        if sol:
            xp,yp = sol
            logging.debug(f"x,y = ({xp},{yp})")
            break
    
    if xp is None: 
        logging.debug("нет хр")
        return None

    mu = lam*j*(C + i*D) + N*(xp + i*yp +j*(zp + i*tp))
    assert mu.reduced_norm() == T
    assert mu in I.left_order()
    logging.debug(f"mu = {mu}")
    return mu, T

import fpylll
from fpylll import IntegerMatrix, CVP
from fpylll.fplll.gso import MatGSO

def generate_CVP(lattice_basis,target,p,T,count=2000):
    """
    Генерация близких векторов
    Вход: базис решетки, цель target, простое p, T
    Выход: генератор близких векторов
    """
    logging.info("#######################")
    logging.info("starting generate_CVP()")
    
    L = IntegerMatrix.from_matrix(lattice_basis.LLL())
    v = CVP.closest_vector(L,target)
    closest = vector(v)
    yield closest

    diff = target - closest
    d = diff.dot_product(diff)

    b0 = floor(T/p)
    B = floor((b0 + d) + sqrt(2*(b0 + d)))
    logging.debug(f"b0 = {b0}, B = {B}")
    short = generate_SVP(lattice_basis,B,count=count)

    for v in short:
        yield closest + v

def generate_SVP(lattice_basis,bound,count=2000):
    """
    Генерация коротких векторов
    Вход: базис решетки, граница bound
    Выход: генератор коротких векторов
    """
    logging.info("#######################")
    logging.info("starting generate_SVP()")
    L = lattice_basis.LLL()
    A = IntegerMatrix.from_matrix(L)

    G = MatGSO(A)
    _ = G.update_gso()

    E = fpylll.Enumeration(G,nr_solutions=count,strategy=fpylll.EvaluatorStrategy.BEST_N_SOLUTIONS)
    r = L.nrows()

    shorts = E.enumerate(0, r, bound, 0)
    for _, xis in shorts:
        v3 = vector([ZZ(xi) for xi in xis])
        short = v3 * L
        yield short

def KLPT(I, T =  2^100*3^2,ex = 2^50):
    """
    Алгоритм KLPT
    Вход: идеал I, целевая норма T, дополнительный множитель ex
    Выход: идеал J, факторизация нормы T и норма T
    """
    logging.info(f"###############")
    logging.info(f"starting KLPT()")
    B = I.quaternion_algebra()
    i,j,k = B.gens()
    O0 = I.left_order()
    p,q = [-ZZ(j**2),-ZZ(i**2)]
    QF = BinaryQF([1,0,q])
    N = ZZ(I.norm())
    factT = T.factor()
    gamma = represent_Integer(N*ex,O0)
    logging.debug(f"gamma = {gamma}\nnorm: {gamma.reduced_norm().factor()}")
    
    alpha = decomp_Alpha_N(I)
    logging.debug(f"alpha = {alpha}")
    
    C,D = ideal_Mod_Constraint(I,gamma,alpha)
    logging.debug(f"C, D = ({C},{D})")
    
    logging.debug(f"factT: {factT}")
    logging.debug(f"I = {I}\nC,D = {C},{D}\nfactT = {factT}")

    mu, T = strong_Approximation(I, C, D, factT)
    logging.debug(f"mu = {mu}\nnorm: {mu.reduced_norm().factor()}")

    beta = gamma*mu
    logging.debug(f"beta = {beta}\nnorm: {beta.reduced_norm().factor()}")

    denom = gcd(O0.unit_ideal().basis_matrix().solve_left((I * (be-ta.conjugate()/N)).basis_matrix()).list())
    
    logging.debug(f"denom = {denom}")
    return_alpha = beta / denom * N / N
    logging.debug(f"ret_alph = {return_alpha}")
    J = I
    J *= return_alpha.conjugate()/I.norm()
    logging.debug(f"J: {J}\nnorm J = {J.norm().factor()}")
    return J, factT, T

def nTorsion_extension_deg(EE,n,psi_n = None):
    """
    Нахождение степени расширения для n-кручения, с предрасчитанной факториза-цией
    многочлена деления
    Вход: кривая E, число n и опциально факторизация многочлена деления
    Выход: степень расширения
    """
    logging.info("###################")
    logging.info("starting nTorsion()")
    if n == 1: return 1
    a,b = [ZZ(EE.a4()),ZZ(EE.a6())]
    p = EE.base_field().characteristic()
    if not psi_n:
        psi_n = EE.division_polynomial(ZZ(n))
        psi_n = factor(EE.division_polynomial(ZZ(n)))
    
    f_i = []
    f_i_deg = []
    for i in range(len(psi_n)):
        f_i.append(psi_n[i][0])
        f_i_deg.append(psi_n[i][0].degree())

    l = lcm(f_i_deg)
    f_i_nuz = []
    
    for i in range(len(f_i)):
        if l%(f_i[i].degree()*2) != 0:
            f_i_nuz = f_i[i]
            d_i = f_i[i].degree()
            if d_i == 1: K = EE.base_field()
            else: K = GF(p^(2*d_i))
            if K == EE.base_field():
                ro = [i[0] for i in f_i_nuz.roots()]
            else:
                ro = [i[0] for i in f_i_nuz.roots(ring = K)]
            func = K(ro[0]^3+a*ro[0]+b)
            if func == 0: continue
            else:
                break

    if not func.is_square(): return 2*l
    else: 
        d_zv = lcm(Mod(p, n).multiplicative_order(),d_i)
        if l == d_zv or l == n*d_zv: return l
        else: return 2*l

def extE(E, extdeg):
    """
    Построение расширения вместе с функцией встраивания 
    оригинального поля в расширенное
    Вход: кривая E и степень расширения
    Выход: расширение кривой E и функция встраивания
    """
    Fbig,emb = E.base_field().extension(extdeg,'A', map=True)
    Ebig = E.change_ring(Fbig)
    return Ebig, emb

def rpt(Eext,cof,l,e):
    """
    Точка нужного порядка
    Вход: расширенная кривая Eext
          #Eext/(l^e) = cof
          кручение l^e
    Выход: точки T и [l]T
    """
    while True:
        T = cof * Eext.random_point()
        Tl = l**(e-1)*T
        if Tl: break
    U = l*Tl
    while U:
        Tl = U
        U *= l
        T *= l
    T.set_order(l**e)
    Tl.set_order(l)
    return T, Tl

def gen_Torsion_Basis(E,Eext,l,e,cof):
    """
    Генерация базиса n-кручения
    Вход: кривая E, расширение Eext, l**e = n, число cof
    Выход: точки P и Q
    """
    P,Pl = rpt(Eext,cof,l,e)
    Q,Ql = rpt(Eext,cof,l,e)
    while Pl.weil_pairing(Ql,l).is_one():
        Q,Ql = rpt(Eext,cof,l,e)
    return P,Q  

def eval_Ideal_Elt(Q,a,E,f,g):
    """
    Расчет a(Q)
    Вход: точка Q, 
          элемент a (I = a*O + N*O), 
          кривая E, 
          (f,g) - функции, 
          определяяющие эндоморфизм f,g
    Выход: точка aQ
    """
    logging.info("#######################")
    logging.info("starting evalIdealElt()")
    p = E.base_field().characteristic()
        
    def eval_i(pt):
        x,y = pt.xy()
        return E(f[0](x,y)/f[1](x,y),g[0](x,y)/g[1](x,y))

    def eval_j(pt):
        x,y = pt.xy()
        return E(x**p,y**p)
    iQ = eval_i(Q)
    jQ = eval_j(Q)
    kQ = eval_i(jQ)
    coeffs = [coeff % Q.order() for coeff in a]
    aQ = coeffs[0]*Q + coeffs[1]*iQ + coeffs[2]*jQ + coeffs[3]*kQ
    return aQ

def Ideal_To_Isogeny_Gens(J,E,iota, st2 = 6, bound = 25,lowbound = 50, diff_poi = False):
    """
    Нахождение ядра изогении
    Вход: идеал J, 
          кривая E, 
          эндоморфизм iota, 
          оптимальная степень двойки st2, 
          границы bound и lowbound для расчета разделения степеней множителей, 
          diff_poi - флаг для генерации различных точек
    Выход: список kerGens
    """
    logging.info("#############################")
    logging.info("starting IdealToIsogenyGens()")

    N = ZZ(J.norm())
    N_fact = N.factor()
    count_deg = []
    for i in N_fact:
        if i[0] == 2:
            osn,st,col,ost = [i[0],st2,i[1]//st2,i[1]%st2]
        else:
            #проверка на оптимальное кручение
            k = 1
            while True:
                if i[0]**k >= bound: break
                k+=1
            if i[0]**k >= lowbound: k -= 1
            if i[0] in [3,7]: k -= 1
            osn,st,col,ost = [i[0],k,i[1]//k,i[1]%k]
        if col:
            logging.debug(f"count psi: {osn}^{st}")
            psi_n = E.division_polynomial(ZZ(i[0]^st)).factor()
        else: psi_n = None
        count_deg.append([osn,st,col,ost,psi_n])

    # содержатся элементы вида [a,st,b,c, psi], 
    # где a - основание степени, st - степень, b - количество степеней st, 
    # c - остаток от деления на st
    # + просчитанный заранее многочлен деления для повторяющихся действий

    kerGens = []
    i,j,k = J.quaternion_algebra().gens()
    a = decomp_Alpha_N(J)
    d = lcm(c.denominator() for c in a)
    p = E.base_field().characteristic()

    def preproc(degree,step,psi_n = None):
        """
        Предвычисления
        Вход: основание степени degree
              показатель степени step
              опциально psi_n
        Выход: l-адическая оценка d lval
               расширенная кривая Eext
               изморфизм из иходной кривой в расширенную emb
               функции эндоморфизма f,g
        """
        lval = d.valuation(degree)
        extdeg = nTorsion_extension_deg(E,degree**(step+lval),psi_n)
        Eext,emb = extE(E,extdeg)
        order = p**extdeg - (-1)**extdeg
        Eext.set_order(order**2,num_checks = 0)

        cof = order.prime_to_m_part(degree)
        f,g = tuple(tuple(g.map_coefficients(emb)
                        for g in (f.numerator(), f.denominator()))
                        for f in iota.rational_maps())
        return lval,Eext,cof,f,g
        

    
    def proschet(Eext,f,g,degree,step,lval,cof):
        """
        Просчет точки ядра изогении
        Вход: расширенная кривая Eext
              функции эндоморфизма f,g
              основание степени degree
              показатель степени step
              порядок расширенной кривой деленный без множителя degree cof
        Выход: точка ядра изогении
        """
        P,Q = gen_Torsion_Basis(E,Eext,degree,step+lval,cof)
        logging.debug(f"P = {P}\nQ = {Q}")
        umnozh = degree**lval*a.conjugate()
        R = eval_Ideal_Elt(P,umnozh,Eext,f,g)
        if not degree**(step-1)*R:
            R = eval_Ideal_Elt(Q,umnozh,Eext,f,g)
        logging.debug(f"R = {R}")
        return R
      

    # далее необходимо пройтись по степеням 
    # [osn,st,col,ost,psi_n]
    # [0   1  2   3   4]
    if diff_poi:
        for deg in count_deg:
            # идем по osn^st: 0^1 col: 2 раз
            logging.debug(f"po stepenyam deg: {deg[0]}")
            if deg[2]:
                logging.debug(f"po stepenyam deg: {deg[0]^deg[1]}")
                lval,Eext,cof,f,g = preproc(deg[0],deg[1],psi_n = deg[4])
                for i in range(deg[2]):
                    while True:
                        G = proschet(Eext,f,g,deg[0],deg[1],lval,cof)
                        if G not in [Eext(0,1,0),Eext(0,0,1)]: break
                    kerGens.append([G,(deg[0],deg[1])])
            # если имеется osn^ost=0^3
            if deg[3]:
                lval,Eext,cof,f,g = preproc(deg[0],deg[1],psi_n = deg[4])
                G = proschet(Eext,f,g,deg[0],deg[1],lval,cof)
                kerGens.append([G,(deg[0],deg[3])])
    else:
        for deg in count_deg:
            # идем по osn^st=0^1 col=2 раз
            logging.debug(f"po stepenyam deg: {deg[0]}")
            if deg[2]:
                #logging.debug(f"torsion = {deg[0]}^{deg[1]}")
                lval,Eext,cof,f,g = preproc(deg[0],deg[1],psi_n = deg[4])
                while True:
                    G = proschet(Eext,f,g,deg[0],deg[1],lval,cof)
                    if G not in [Eext(0,1,0),Eext(0,0,1)]: break
                
                for i in range(deg[2]):
                    kerGens.append([G,(deg[0],deg[1])])
            # если имеется osn^ost=0^3
            if deg[3]:
                lval,Eext,cof,f,g = preproc(deg[0],deg[1],psi_n = deg[4])
                G = proschet(Eext,f,g,deg[0],deg[1],lval,cof)
                kerGens.append([G,(deg[0],deg[3])])
            
    return kerGens

def kernel_Polynomial(E,pt,l):
    """
    Расчет многочлена ядра изогении

    Вход: кривая E, точка ядра pt, множитель l

    Выход: многочлен ядра
    """
    F2 = E.base_field()
    Fbig = pt.curve().base_field()
    ext = Fbig.over(F2)
    x = pt.x()
    extX = ext(x)

    f = extX.minpoly()
    if l <= 3:
        return f
    
    k = f.degree()
    m = floor(l/2*k)

    fs  = [f]
    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive
    a = _least_semi_primitive(l)
    pti = pt 
    for i in range(2,m):
        pti = pti*a
        fs.append(pti.x().minpoly())
    return prod(fs)

def iso_From_Poly(E,pt,l):
    """
    Изогения из многочлена ядра изогении
    Вход: кривая E, точка ядра pt, множитель l
    Выход: изогения
    """
    f = kernel_polynomial(E,pt,l)
    return E.isogeny(f,check = False)

"""
Запуск
Работает на версии sage 10.4
"""
p = 30*2**30-1
E,iota,q = constr_EC(p)
E = E.change_ring(GF(p^2))
order_E_fact = E.order().factor()

O = QuaternionAlgebra(-q,-p).maximal_order()
O0 = constr_Max_Order(p,q)
O0 = list(O0.values())

I = connecting_Ideal(O,O0[0])
I_equiv = equivalent_Prime_Ideal(I)

T_ = 1
for i in order_E_fact:
    if i[0] < 10:
        if i[0] != 2:
            T_ *= i[0]**randint(40,50)

J,factT,T = KLPT(I_equiv,T = T_)

kerGens = Ideal_To_Isogeny_Gens(J,E,iota,diff_poi = False)


