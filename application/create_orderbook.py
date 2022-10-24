################  Generate ###############
import random
def generate(prob_ins, n = 10, prob_update = 0):
    id_current = 1
    id_prev = 1
    instructions = ['' for _ in range(n)]
    quantities = [0 for _ in range(n)]
    prices = [0 for _ in range(n)]
    ids = [0 for _ in range(n)]
    times = list(range(n))
    i = 0    
    while(i < n):
        ins_current = random.choices(k = 1, population = list(prob_ins.keys()), weights = list(prob_ins.values())).pop()
        if(ins_current != 'Del'):
            id_current = id_prev + 1
        instructions[i] = ins_current
        ids[i] = id_current
        quantities[i] = random.randint(1, 10000)
        prices[i] = random.randint(10000, 20000)
        id_prev = id_current
        i += 1
    concat_func = lambda a, b, c, d, e: a + "," + str(b)+ "," + str(c)+ "," + str(d)+ "," + str(e)
    orderbook = list(map(concat_func, instructions, ids, times, quantities, prices)) # list the map function
    return(orderbook)
#This will generate two order books of sizes 100K and 200K. Modify this as desired.
sizes = [100000, 200000]
#Uncomment the following three lines to generate order books of sizes ranging from 200K to 10M.
##M = 10000000
##L = 200000
##sizes = list(range(L, M+1, L))
prob_ins = {'Del': 1/3, 'Buy':1/3, 'Sell':1/3}
for n in sizes:
    orderbook = generate(prob_ins, n)
    data = '\n'.join(orderbook)
    file = "orderbook_" + str(n)
    f = open(file, 'w')
    f.write(data)
    f.close()
    
