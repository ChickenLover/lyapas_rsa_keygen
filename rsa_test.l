main(/)
    T⇒X
    Oi 5000⇒s
    §1 ↑(i=s)2 *gen_keys(/d,e,n) ∆i →1
    §2 
        /'Initial text: '>C *printarray(L1/)
        /'e: '>C *printint(e/) /'\n'>C
        /'d: '>C *printint(d/) /'\n'>C
        /'n: '>C *printint(n/) /'\n'>C
    **


gen_keys(/d,e,n)
    *gen_prime(1,65536/p)
    *gen_prime(1,65536/q)
    p*q⇒n
    ∇p ∇q p*q⇒f-1⇒j
    §1 X;j+1⇒e *gcd(e,f/d) ↑(d≠1)1
    *ext_gcd(f,e/x,d,s)
    ↑(s=1)2 f-d⇒d §2
    **


check_keys(d,e,n/b)
    @+L1(50)
    *gen_random_array(0,n,50,L1/L1)
    ***/'Initial text: '>C *printarray(L1/)
    @+L2(50) *rsa_encode(L1,e,n/L2) ***/'Cypher text: '>C *printarray(L2/)
    @+L3(50) *rsa_encode(L2,d,n/L3) ***/'Decrypted text: '>C *printarray(L3/)
    *arrcomp(L1,L3/b)
    **


gen_random_array(f,t,s,L1/L1)
    Oi
    §1 ↑(i=s)2 *gen_random(f,t/n) ∆i n@>L1 →1
    §2 **


gen_random(f,t/n)
    X⇒n n;t⇒n n+f⇒n **

gen_prime(f,t/n)
    §1 *gen_random(f,t/n) n;2↪1
    *if_prime_miller_rabin(n,32/b) b↪1 **

decompose_into_power_of_two(n/s,t)
    Os n⇒p
    §1 p/2⇒r ∆s r;2↦2 r⇒p →1
    §2 *pow(2,s/p) n/p⇒t**

if_prime_miller_rabin(n,k/b)
    Ob ↑(n=2)3
    n-1⇒d *decompose_into_power_of_two(d/s,t)
    §1 k↪3 ∇k
        *gen_random(2,d/a)
        *pow_mod(a,t,n/x)
        ↑(x=1)1 ↑(x=d)1
        s-1⇒i
        §2 i↪4 ∇i
            *pow_mod(x,2,n/x)
            ↑(x=1)4 ↑(x=d)1 →2
        →4
    §3 1⇒b
    §4 **

pow(a,n/r)
    1⇒r
    §1 n↪2 ∇n  
        r*a⇒r →1
    §2 **






mul_mod(a,b,m/r)
    a*b:m Z⇒r **

pow_mod(a,b,m/r)
    Or a↪3 b↦1 1⇒r →3
    §1 b;2↦2 b/2⇒h *pow_mod(a,h,m/r) *mul_mod(r,r,m/r) →3
    §2 b-1⇒h *pow_mod(a,h,m/r) *mul_mod(r,a,m/r)
    §3 **


ext_gcd(a,b/x,y,s)
    Os *ext_gcd_signed(a,b,s/x,y,s)

ext_gcd_signed(a,b,s/x,y,s)
    b↦1 1⇒x 0⇒y →5
    §1 a;b⇒i
    *ext_gcd_signed(b,i,s/m,n,s)
    a/b*n⇒t n⇒x ↑(s=2)4
       ↑(s=1)3 
       ↑(m<t)2 m-t⇒y →5 ***y = k1 - a/b*k2     a/b*k2<=k1
       §2 t-m⇒y 2⇒s →5  ***y = k1 - a/b*k2     a/b*k2>k1
       §3 m+t⇒y 2⇒s →5  ***y = -k1 - a/b*k2
    §4 m+t⇒y 1⇒s *** y = k1 + a/b*k2
    §5**

gcd(a,b/d)
    §1 ↑(a≥b)2
    b;a⇒b →3
    §2 a;b⇒a
    §3 a↪4 b↪4 →1
    §4 a+b⇒d
    **

rsa_encode(L1,e,n/L2)
    Oi
    §1 ↑(Q1=i)2 L1i⇒c ∆i
    *pow_mod(c,e,n/r)
    r @>L2 →1
    §2**

stoi(F1/i)
    Oi
§1  i*10⇒ i
    @<F1.0-48+i⇒ i
    Q1↦1
    **

arrcomp(L1,L2/b)
    Ob ↑(Q1≠Q2)3 Oi
    §1 ↑(i=Q1)2 ↑(L1i≠L2i)3 ∆i →1
    §2 1⇒b
    §3 **


strcomp(F1,F2/b)
    Ob ↑(Q1≠Q2)3 Oi
    §1 ↑(i=Q1)2 ↑(F1i≠F2i)3 ∆i →1
    §2 1⇒b
    §3 **


itos(i/F1)
§1  i;10 + 48@>F1.0
    Z⇒ i
    i↦1
    **

printint(i/)
    @+F1(16)
    *itos(i/F1)
    /F1>C /' '>C **


printarray(L1/)
    Oi
§1  ↑(i=Q1)2
    *printint(L1i/)
    ∆i →1
§2 /'\n'>C **
