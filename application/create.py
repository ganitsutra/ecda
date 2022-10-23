f = open("orderbook1", 'r')
ell = f.readline()
#orderbook = []
ins = {'Buy':0,'Sell':0,'Del':0}
qty = dict()
pr = dict()
previd = ''
count = 0
while(ell):
    ell = ell.replace('\n', '')
    order = ell.split(',') # instruction, id, time, quantity, price
    order = [order[0]] + [int(order[i]) for i in [1,2,3,4]]
    ins[order[0]] += 1
    if(qty.__contains__(order[3])):
        qty[order[3]] += 1
    else:
        qty[order[3]] = 1
    if(pr.__contains__(order[4])):
        pr[order[4]] += 1
    else:
        pr[order[4]] = 1
    if(previd == order[1]):
        count += 1
    previd = order[1]
    #orderbook.append((order[0],int(order[1]),int(order[2]),int(order[3]),int(order[4])))
    ell = f.readline()

f.close()


################  Generate ###############
import random
total = sum(ins.values())
prob_update = count/total
#prob_ins = {key: ins[key]/total for key in ins.keys()}
prob_ins = {'Del': 1/3, 'Buy':1/3, 'Sell':1/3}
def generate(prob_ins, n = 10, prob_update = 0):
    id_current = 1
    id_prev = 1
    #ins_prev = 'Del'
    instructions = ['' for _ in range(n)]
    quantities = [0 for _ in range(n)]
    prices = [0 for _ in range(n)]
    ids = [0 for _ in range(n)]
    times = list(range(n))
    i = 0    
    while(i < n):
        ins_current = random.choices(k = 1, population = list(prob_ins.keys()), weights = list(prob_ins.values())).pop()
        #if(ins_current == 'Del' and ins_prev == 'Del'):
        #    continue
        if(ins_current != 'Del'):
            id_current = id_prev + 1
        instructions[i] = ins_current
        ids[i] = id_current
        quantities[i] = random.randint(1, 10000)
        prices[i] = random.randint(10000, 20000)
        id_prev = id_current
        #ins_prev = ins_current
        i += 1
    concat_func = lambda a, b, c, d, e: a + "," + str(b)+ "," + str(c)+ "," + str(d)+ "," + str(e)
    orderbook = list(map(concat_func, instructions, ids, times, quantities, prices)) # list the map function
    return(orderbook)
    #int(random.random() > update)

M = 10000000
L = 200000
sizes = list(range(L, M+1, L))
for n in sizes:
    orderbook = generate(prob_ins, n)
    data = '\n'.join(orderbook)
    file = "/home/suneel/Documents/application/data/orderbook_" + str(n)
    f = open(file, 'w')
    f.write(data)
    f.close()
    
