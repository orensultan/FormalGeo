# formalgeo7k

We’ve annotated the formalgeo7k datasets based on [Formalgeo](https://github.com/FormalGeo/FormalGeo), which contains
6,981 plane geometric problems. Each problem comprises a complete natural language description, geometric shapes, formal
language annotations, and theorem sequences annotations.

Collaborative annotation project can be found in [here](https://github.com/BitSecret/formalgeo7k).

More information about FormalGeo will be found in [homepage](https://formalgeo.github.io/). FormalGeo is in its early
stages and brimming with potential. We welcome anyone to join us in this exciting endeavor.

## Annotation Example

```json
{
  "problem_id": 1,
  "problem_text_cn": "如图所示，三角形RST与三角形XYZ是全等三角形，TR=x+21，ZX=2*x-14，∠TRS=4*y-10°，∠ZXY=3*y+5°。求y的值。",
  "problem_text_en": "As shown in the diagram, triangle RST is congruent to triangle XYZ, TR=x+21, ZX=2*x-14, ∠TRS=4*y-10°, ∠ZXY=3*y+5°. Find the value of y.",
  "problem_img": "1.png",
  "construction_cdl": [
    "Shape(RS,ST,TR)",
    "Shape(XY,YZ,ZX)"
  ],
  "text_cdl": [
    "CongruentBetweenTriangle(RST,XYZ)",
    "Equal(LengthOfLine(TR),x+21)",
    "Equal(LengthOfLine(ZX),2*x-14)",
    "Equal(MeasureOfAngle(TRS),4*y-10)",
    "Equal(MeasureOfAngle(ZXY),3*y+5)"
  ],
  "image_cdl": [
    "Equal(LengthOfLine(TR),x+21)",
    "Equal(LengthOfLine(ZX),2*x-14)",
    "Equal(MeasureOfAngle(TRS),4*y-10)",
    "Equal(MeasureOfAngle(ZXY),3*y+5)"
  ],
  "goal_cdl": "Value(y)",
  "problem_answer": "15",
  "theorem_seqs": [
    "congruent_triangle_property_angle_equal(1,RST,XYZ)"
  ]
}
```

## Contributors

6981 problems contributed by 16 authors:

XiaokaiZhang <xiaokaizhang1999@163.com> (764, 10.94%)  
NaZhu <nazhu@shu.edu.cn> (741, 10.61%)  
YimingHe <hym123@shu.edu.cn> (714, 10.23%)  
JiaZou <zouj@shu.edu.cn> (709, 10.16%)  
QikeHuang <qkhuang112@163.com> (476, 6.82%)  
XiaoxiaoJin <leo_jxx@163.com> (446, 6.39%)  
YanjunGuo <yanjunguo@163.com> (439, 6.29%)  
ChenyangMao <shadymao@shu.edu.com> (432, 6.19%)  
YangLi <laying2000@outlook.com> (414, 5.93%)  
ZheZhu <zhuzhe@shu.edu.cn> (414, 5.93%)  
DengfengYue <ydf@shu.edu.cn> (403, 5.77%)  
FangzhenZhu <zhufz@shu.edu.cn> (267, 3.82%)  
YifanWang <wangyifan0216@shu.edu.cn> (218, 3.12%)  
YiwenHuang <15967121844@163.com> (185, 2.65%)  
RunanWang <luckyrunan@163.com> (181, 2.59%)  
ChengQin <karllonrenz@outlook.com> (178, 2.55%)

## Source

Our original geometric problems are sourced
from [Geometry3K](https://github.com/lupantech/InterGPS), [GeoQA](https://github.com/chen-judge/GeoQA), [GeoQA+](https://github.com/SCNU203/GeoQA-Plus)
and online resources.

## Citation

To cite formalgeo7k in publications use:
> Zhang X, Zhu N, He Y, et al. FGeo-SSS: A Search-Based Symbolic Solver for Human-like Automated Geometric Reasoning[J].
> Symmetry, 2024, 16(4): 404.

A BibTeX entry for LaTeX users is:
> @article{zhang2024fgeosss,  
> AUTHOR = {Zhang, Xiaokai and Zhu, Na and He, Yiming and Zou, Jia and Qin, Cheng and Li, Yang and Leng, Tuo},  
> TITLE = {FGeo-SSS: A Search-Based Symbolic Solver for Human-like Automated Geometric Reasoning},  
> JOURNAL = {Symmetry},  
> VOLUME = {16},  
> YEAR = {2024},  
> NUMBER = {4},  
> ARTICLE-NUMBER = {404},  
> URL = {https://www.mdpi.com/2073-8994/16/4/404},  
> ISSN = {2073-8994},  
> DOI = {10.3390/sym16040404}  
> }
