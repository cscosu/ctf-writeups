import time
import Crypto.Util.number as cun
import os

debug = True

# display matrix picture with 0 and X
def matrix_overview(BB, bound):
    for ii in range(BB.dimensions()[0]):
        a = ('%02d ' % ii)
        for jj in range(BB.dimensions()[1]):
            a += '0' if BB[ii,jj] == 0 else 'X'
            a += ' '
        if BB[ii, ii] >= bound:
            a += '~'
        print(a)

def coppersmith_howgrave_univariate(pol, modulus, beta, mm, tt, XX):
    """
    Coppersmith revisited by Howgrave-Graham

    finds a solution if:
    * b|modulus, b >= modulus^beta , 0 < beta <= 1
    * |x| < XX
    """
    #
    # init
    #
    dd = pol.degree()
    nn = dd * mm + tt

    #
    # checks
    #
    if not 0 < beta <= 1:
        raise ValueError("beta should belongs in (0, 1]")

    if not pol.is_monic():
        raise ArithmeticError("Polynomial must be monic.")

    #
    # calculate bounds and display them
    #
    """
    * we want to find g(x) such that ||g(xX)|| <= b^m / sqrt(n)

    * we know LLL will give us a short vector v such that:
    ||v|| <= 2^((n - 1)/4) * det(L)^(1/n)

    * we will use that vector as a coefficient vector for our g(x)

    * so we want to satisfy:
    2^((n - 1)/4) * det(L)^(1/n) < N^(beta*m) / sqrt(n)

    so we can obtain ||v|| < N^(beta*m) / sqrt(n) <= b^m / sqrt(n)
    (it's important to use N because we might not know b)
    """
    if debug:
        # t optimized?
        print("\n# Optimized t?\n")
        print("we want X^(n-1) < N^(beta*m) so that each vector is helpful")
        cond1 = RR(XX^(nn-1))
        print("* X^(n-1) = ", cond1)
        cond2 = pow(modulus, beta*mm)
        print("* N^(beta*m) = ", cond2)
        print("* X^(n-1) < N^(beta*m) \n-> GOOD" if cond1 < cond2 else "* X^(n-1) >= N^(beta*m) \n-> NOT GOOD")

        # bound for X
        print("\n# X bound respected?\n")
        print("we want X <= N^(((2*beta*m)/(n-1)) - ((delta*m*(m+1))/(n*(n-1)))) / 2 = M")
        print("* X =", XX)
        cond2 = RR(modulus^(((2*beta*mm)/(nn-1)) - ((dd*mm*(mm+1))/(nn*(nn-1)))) / 2)
        print("* M =", cond2)
        print("* X <= M \n-> GOOD" if XX <= cond2 else "* X > M \n-> NOT GOOD")

        # solution possible?
        print("\n# Solutions possible?\n")
        detL = RR(modulus^(dd * mm * (mm + 1) / 2) * XX^(nn * (nn - 1) / 2))
        print("(e can find a solution if 2^((n - 1)/4) * det(L)^(1/n) < N^(beta*m) / sqrt(n))")
        cond1 = RR(2^((nn - 1)/4) * detL^(1/nn))
        print("* 2^((n - 1)/4) * det(L)^(1/n) = ", cond1)
        cond2 = RR(modulus^(beta*mm) / sqrt(nn))
        print("* N^(beta*m) / sqrt(n) = ", cond2)
        print("* 2^((n - 1)/4) * det(L)^(1/n) < N^(beta*m) / sqrt(n) \n-> SOLUTION WILL BE FOUND" if cond1 < cond2 else "* 2^((n - 1)/4) * det(L)^(1/n) >= N^(beta*m) / sqroot(n) \n-> NO SOLUTIONS MIGHT BE FOUND (but we never know)")

        # warning about X
        print("\n# Note that no solutions will be found _for sure_ if you don't respect:\n* |root| < X \n* b >= modulus^beta\n")

    #
    # Coppersmith revisited algo for univariate
    #

    # change ring of pol and x
    polZ = pol.change_ring(ZZ)
    x = polZ.parent().gen()

    # compute polynomials
    gg = []
    for ii in range(mm):
        for jj in range(dd):
            gg.append((x * XX)**jj * modulus**(mm - ii) * polZ(x * XX)**ii)
    for ii in range(tt):
        gg.append((x * XX)**ii * polZ(x * XX)**mm)

    # construct lattice B
    BB = Matrix(ZZ, nn)

    for ii in range(nn):
        for jj in range(ii+1):
            BB[ii, jj] = gg[ii][jj]

    # display basis matrix
    if debug:
        matrix_overview(BB, modulus^mm)

    # LLL
    BB = BB.LLL()

    # transform shortest vector in polynomial
    new_pol = 0
    for ii in range(nn):
        new_pol += x**ii * BB[0, ii] / XX**ii

    # factor polynomial
    potential_roots = new_pol.roots()
    print("potential roots:", potential_roots)

    # test roots
    roots = []
    for root in potential_roots:
        if root[0].is_integer():
            result = polZ(ZZ(root[0]))
            if gcd(modulus, result) >= modulus^beta:
                roots.append(ZZ(root[0]))

    #
    return roots

def lower_bytes(x, nbytes):
    return cun.bytes_to_long(cun.long_to_bytes(x)[-nbytes:])

# Public key
N = 13876129555781460073002089038351520612247655754841714940325194761154811715694900213267064079029042442997358889794972854389557630367771777876508793474170741947269348292776484727853353467216624504502363412563718921205109890927597601496686803975210884730367005708579251258930365320553408690272909557812147058458101934416094961654819292033675534518433169541534918719715858981571188058387655828559632455020249603990658414972550914448303438265789951615868454921813881331283621117678174520240951067354671343645161030847894042795249824975975123293970250188757622530156083354425897120362794296499989540418235408089516991225649
length_N = 2048
ZmodN = Zmod(N);
e = 3

# Obscuring term (was called `x` previously)
obs = 15581107453382746363421172426030468550126181195076252322042322859748260918197659408344673747013982937921433767135271108413165955808652424700637809308565928462367274272294975755415573706749109706624868830430686443947948537923430882747239965780990192617072654390726447304728671150888061906213977961981340995242772304458476566590730032592047868074968609272272687908019911741096824092090512588043445300077973100189180460193467125092550001098696240395535375456357081981657552860000358049631730893603020057137233513015505547751597823505590900290756694837641762534009330797696018713622218806608741753325137365900124739257740
length_obs = 440

# Ciphertext
C = 6581985633799906892057438125576915919729685289065773835188688336898671475090397283236146369846971577536055404744552000913009436345090659234890289251210725630126240983696894267667325908895755610921151796076651419491871249815427670907081328324660532079703528042745484899868019846050803531065674821086527587813490634542863407667629281865859168224431930971680966013847327545587494254199639534463557869211251870726331441006052480498353072578366929904335644501242811360758566122007864009155945266316460389696089058959764212987491632905588143831831973272715981653196928234595155023233235134284082645872266135170511490429493

# Obsuring term with lower 440 bits zero'd (was called 'b' previously)
obs_clean = (obs >> length_obs) << length_obs

# Problem to equation.
# The `x` here was called `a` previously, which we are now solving for.
P.<x> = PolynomialRing(ZmodN)
pol = (obs_clean + x)^e - C
dd = pol.degree()

beta = 1                                # b = N
epsilon = beta / 7                      # <= beta / 7
mm = ceil(beta**2 / (dd * epsilon))     # optimized value
tt = floor(dd * mm * ((1/beta) - 1))    # optimized value
XX = ceil(N**((beta**2/dd) - epsilon))  # optimized value

# Coppersmith
roots = coppersmith_howgrave_univariate(pol, N, beta, mm, tt, XX)

print()
print("Solutions")
print("We found:", str(roots))
