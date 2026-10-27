import subprocess, json, sys, os
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
lines = [l for l in open('rep/m11_search.log') if l.startswith('HIT') and ' z=0 ' in l]
if not lines:
    raise SystemExit('M11_CHECK FAIL: no witness supplied')
res = []
for n, line in enumerate(lines):
    kv = dict(t.split('=', 1) for t in line.split()[1:])
    co = [tuple(map(int, c.split(':'))) for c in kv['coeffs'].split(',')]
    fn = f'rep/m11_rep{n}_nat.txt'
    with open(fn, 'w') as f:
        f.write(f'{len(co)}\n')
        for e, c in co:
            f.write(f'{e} ' + ' '.join(str((c >> i) & 1) for i in range(11)) + '\n')
    j = json.loads(subprocess.run(['python3', 'inv.py', '11', fn], capture_output=True, text=True, check=True).stdout)
    r = dict(n=n, search_rho=int(kv['rho']), search_mu=int(kv['mu']), search_z=int(kv['z']),
             inv_rho=j.get('rho'), inv_mu=j.get('mu'), inv_absZ=len(j.get('Z', [])),
             A_zeros=(j['A'].count(0) if 'A' in j else None), degree=max(e for e, _ in co), terms=len(co))
    res.append(r); print(json.dumps(r), flush=True)
ok = all(r['inv_mu'] == 0 and r['inv_absZ'] == 0 and r['inv_rho'] == r['search_rho'] for r in res)
json.dump(res, open('rep/m11_check.json', 'w'), indent=1)
print('M11_CHECK', 'OK' if ok else 'FAIL', len(res))

if not ok:
    raise SystemExit(1)
