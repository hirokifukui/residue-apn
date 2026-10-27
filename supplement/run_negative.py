# R04-06: negative controls for validate_v3.py. Every case below must make validate_v3 exit non-zero;
# the two positive controls must exit 0. 8 fake checkers (child-output faults) + 9 scope/expectation faults.
import subprocess, json, os, sys
here=os.path.dirname(os.path.abspath(__file__)); os.chdir(here)
subprocess.run(['sh','neg/mk.sh'],check=True)
def run(args, extra):
    env=os.environ.copy(); env['VOUT']='/dev/null'; env.setdefault('VK','3')
    for k,v in extra.items():
        if v is None: env.pop(k,None)
        else: env[k]=v
    return subprocess.run([sys.executable,'validate_v3.py']+args,capture_output=True,text=True,env=env)
out=[]; bad=0
for c in ['exit7','empty','header_only','nonperm','dupdir','badclass','badmass','partial']:
    p=run(['c0_A1.txt'],{'GRDDT':os.path.join(here,'neg',c+'.sh')})
    out.append(dict(case='checker_'+c,expect='reject',exit=p.returncode,tail=p.stderr.strip().splitlines()[-1:]))
    bad+=(p.returncode==0)
scope=[('no_input_files',[],{}),('unsupported_level_VK6',['c0_A1.txt'],{'VK':'6'}),
       ('duplicate_level_VK33',['c0_A1.txt'],{'VK':'3,3'}),('empty_level_VK',['c0_A1.txt'],{'VK':''}),
       ('unsupported_m_VM9',['c0_A1.txt'],{'VM':'9'}),('missing_input_file',['no_such_file.txt'],{}),
       ('bad_VMODE3',['c0_A1.txt'],{'VMODE3':'all'}),('wrong_VEXPECT_MATCH',['c0_A1.txt'],{'VEXPECT_MATCH':'2'}),
       ('bound_only_without_match',['c1_o3.txt'],{'VK':'4'})]
for name,args,extra in scope:
    p=run(args,extra)
    out.append(dict(case=name,expect='reject',exit=p.returncode,tail=p.stderr.strip().splitlines()[-1:]))
    bad+=(p.returncode==0)
for name,args,extra in [('positive_real_checker',['c0_A1.txt'],{}),('positive_expect_pinned',['c0_A1.txt'],{'VEXPECT_MATCH':'1','VEXPECT_BOUND':'0'})]:
    p=run(args,extra)
    out.append(dict(case=name,expect='accept',exit=p.returncode,tail=p.stdout.strip().splitlines()[-1:]))
    bad+=(p.returncode!=0)
json.dump(out,open('negative_controls.json','w'),indent=1)
for r in out: print(r)
if bad: print('NEGATIVE_CONTROLS FAIL',bad); sys.exit(1)
print('NEGATIVE_CONTROLS OK',sum(1 for r in out if r['expect']=='reject'),'rejected,',sum(1 for r in out if r['expect']=='accept'),'accepted')
