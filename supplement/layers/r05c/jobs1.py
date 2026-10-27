import json
J=[]
for base,u1,u2 in [('r1010_A0',6,5),('r1011_A0',5,9)]:
    for sd,sn in enumerate(['res_i0','res_i1','nonres_ia','nonres_ib','nonres']):
        J.append([base,7,2,u2,100+sd,sn])
    for sd,sn in enumerate(['res_i1_d2q','res_i1_d2s0','res_i1_d2s1','res_i1_d2s2','res_i0','nonres_ia']):
        J.append([base,8,2,u2,200+sd,sn]); J.append([base,7,1,u1,300+sd,sn])
    for sd,sn in enumerate(['res_i1_nonres','res_i1_res_i1','res_i1_res_i0','nonres_ia','nonres_ib']):
        J.append([base,8,1,u1,400+sd,sn])
print(json.dumps(J))
