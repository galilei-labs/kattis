#!/usr/bin/env python3
"""Plot measured timings; any requested FFT extrapolation is separate and dotted."""
from pathlib import Path
from collections import defaultdict
import csv, json, statistics
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, NullFormatter
import numpy as np

HERE = Path(__file__).resolve().parent
records = defaultdict(lambda: defaultdict(list))
for source in [HERE/'raw.csv', HERE/'fft-large.csv', HERE/'schoolbook-large.csv']:
    if not source.exists(): continue
    with source.open() as f:
        for row in csv.DictReader(f):
            records[int(row['total_coefficients'])][row['algorithm']].append(float(row['seconds_per_call']))
ns = {a:np.array(sorted(n for n in records if len(records[n][a])==7)) for a in ['schoolbook','fft']}
assert all(ns[a].size for a in ns)
median = {a: np.array([statistics.median(records[n][a])*1000 for n in ns[a]]) for a in ns}
spread = {a: np.array([np.percentile(records[n][a], [25,75])*1000 for n in ns[a]]) for a in ns}
shared = sorted(set(ns['schoolbook']) & set(ns['fft']))
ratios={n:statistics.median(records[n]['schoolbook'])/statistics.median(records[n]['fft']) for n in shared}
first=next(n for n in shared if ratios[n]>1)
metadata = json.loads((HERE/'metadata.json').read_text())
metadata['matplotlib_version'] = matplotlib.__version__
(HERE/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
with (HERE/'summary.csv').open('w') as f:
    w=csv.writer(f)
    w.writerow(['total_coefficients','coefficients_per_input','schoolbook_median_ms','fft_median_ms','fft_speedup','schoolbook_q25_ms','schoolbook_q75_ms','fft_q25_ms','fft_q75_ms'])
    for n in sorted(set(ns['schoolbook'])|set(ns['fft'])):
        values={a:[statistics.median(records[n][a])*1000,*np.percentile(records[n][a],[25,75])*1000] if len(records[n][a])==7 else ['','',''] for a in ns}
        w.writerow([n,n//2,values['schoolbook'][0],values['fft'][0],ratios.get(n,''),*values['schoolbook'][1:],*values['fft'][1:]])

extension=json.loads((HERE/'fft-extension.json').read_text()) if (HERE/'fft-extension.json').exists() else None
stopped=extension and any(x['status']=='stopped' for x in extension['sizes'])
kattis_max=262144
extrap_x=extrap_y=None
if stopped and ns['fft'][-1]<kattis_max:
    # Anchor N log2 N scaling at the last measured point; N is the FFT's padded length.
    extrap_x=np.unique(np.r_[ns['fft'][-1],np.geomspace(ns['fft'][-1],kattis_max,100).astype(int),kattis_max])
    lengths=2.**np.ceil(np.log2(extrap_x-1))
    work=lengths*np.log2(lengths)
    extrap_y=median['fft'][-1]*work/work[0]
    with (HERE/'fft-extrapolation.csv').open('w') as f:
        w=csv.writer(f);w.writerow(['total_coefficients','estimated_ms','method'])
        w.writerows((n,t,'last measured time scaled by padded FFT length * log2(length)') for n,t in zip(extrap_x,extrap_y))
elif (HERE/'fft-extrapolation.csv').exists():
    (HERE/'fft-extrapolation.csv').unlink()

schoolbook_x=schoolbook_y=None
if (HERE/'schoolbook-extension.json').exists() and ns['schoolbook'][-1]<kattis_max:
    schoolbook_x=np.geomspace(ns['schoolbook'][-1],kattis_max,100)
    schoolbook_y=median['schoolbook'][-1]*(schoolbook_x/ns['schoolbook'][-1])**2
    with (HERE/'schoolbook-extrapolation.csv').open('w') as f:
        w=csv.writer(f);w.writerow(['total_coefficients','estimated_ms','method'])
        w.writerows((n,t,'quadratic scaling anchored at last measured schoolbook point') for n,t in zip(schoolbook_x,schoolbook_y))

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.labelcolor':'#263446',
                     'text.color':'#1d2d44','axes.edgecolor':'#d4dce5','svg.fonttype':'path'})
fig,ax = plt.subplots(figsize=(12,7.2))
fig.subplots_adjust(left=.10,right=.97,top=.78,bottom=.24)
fig.text(.10,.94,'Extracted OCaml: schoolbook vs FFT',fontsize=23,weight='bold')
fig.text(.10,.895,'Equal-size integer polynomials · median of 7 trials · shaded bands show the interquartile range',fontsize=11,color='#5c6b7d')
if ns['fft'][-1]==kattis_max:
    headline=(f'At maximum Kattis degree: FFT {median["fft"][-1]/1000:.2f} s measured; schoolbook {schoolbook_y[-1]/1000:.0f} s estimated.'
              if schoolbook_y is not None else f'FFT at the maximum Kattis degree (131,071): {median["fft"][-1]/1000:.2f} s per multiplication.')
elif stopped:
    headline='Solid lines are measured; the dotted FFT extension is an estimate beyond the last completed size.'
else:
    headline=f'First measured FFT win: {first//2:,} coefficients per input; {ratios[shared[-1]]:.1f}× faster at {shared[-1]//2:,}.'
fig.text(.10,.845,headline,fontsize=13)
colors={'schoolbook':'#325bba','fft':'#15925d'}
for a,label in [('schoolbook','Schoolbook'),('fft','FFT')]:
    ax.fill_between(ns[a],spread[a][:,0],spread[a][:,1],color=colors[a],alpha=.16,linewidth=0)
    ax.plot(ns[a],median[a],'-o',color=colors[a],lw=2.2,ms=4,label=label)
if extrap_x is not None:
    ax.plot(extrap_x,extrap_y,':',color=colors['fft'],lw=2.4,label='FFT extrapolation (not measured)')
if schoolbook_x is not None:
    ax.plot(schoolbook_x,schoolbook_y,':',color=colors['schoolbook'],lw=2.4,label='Schoolbook extrapolation')
ax.set_xscale('log',base=2);ax.set_yscale('log')
xmax=kattis_max if stopped else max(ns['fft'][-1],ns['schoolbook'][-1])
ticks=[32,128,512,2048,8192,32768] if xmax<=32768 else [32,256,2048,16384,262144]
ax.set_xticks(ticks);ax.xaxis.set_major_formatter(FuncFormatter(lambda v,p:f'{v:,.0f}'))
ymax=max(max(median[a]) for a in median)
if extrap_y is not None:ymax=max(ymax,max(extrap_y))
if schoolbook_y is not None:ymax=max(ymax,max(schoolbook_y))
ax.set_yticks(10.**np.arange(-3,int(np.floor(np.log10(ymax)))+1));ax.yaxis.set_major_formatter(FuncFormatter(lambda v,p:f'{v:,.0f}' if v>=1 else f'{v:g}'))
ax.yaxis.set_minor_formatter(NullFormatter())
ax.set_xlabel('Total input coefficients n (n/2 coefficients per polynomial)',labelpad=12)
ax.set_ylabel('Time per multiplication (ms)',labelpad=10)
ax.grid(which='major',color='#e7ebf0',linewidth=.8);ax.set_axisbelow(True)
ax.spines[['top','right']].set_visible(False)
ax.legend(loc='upper left',frameon=False,fontsize=11)
ax.set_xlim(min(ns['fft'][0],ns['schoolbook'][0])*.85,xmax*1.20)
fig.text(.10,.145,f"{metadata['machine']} · OCaml {metadata['ocaml_version']} native (-O3) · signed coefficients in [−3, 3]",fontsize=10,color='#5c6b7d')
fig.text(.10,.105,'Solid curves: measured. Dotted schoolbook extension: quadratic estimate; FFT uses power-of-two padding.',fontsize=10,color='#5c6b7d')
footer='Marray backend (unverified extraction). Schoolbook spec limit: 256 coefficients/input. Validation details in README.' if extension else 'Upstream Marray backend (not a verified extraction). All 126 tested output pairs match.'
fig.text(.10,.065,footer,fontsize=10,color='#5c6b7d')
for ext in ['png','svg','pdf']:
    fig.savefig(HERE/f'polymul-benchmark.{ext}',dpi=200,facecolor='white')
print(headline)
print('Measured FFT maximum:',ns['fft'][-1]//2,'coefficients per input;',median['fft'][-1],'ms')
