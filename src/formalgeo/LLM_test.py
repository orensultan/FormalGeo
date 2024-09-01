import time
import openai
import json

import numpy as np

openai.api_key = "sk-svcacct-kVTUGOlCTL2vge6gtHi--la5vr8g-lqT3ieuWGdHQBrYChItgkm2k1WPS9mA-MXe7ebaPHCMk8YrCft1OT3BlbkFJLNl-eYBXpQiokB5m3Nw0oiO9ZOe_Paf1WH0Kh4If52-rQ92DiSodgoopxiDoQDKlAGYDPRpiWamueq8vQA"
theorems_file_path = "formalgeo7k_v1/gdl/theorem_GDL.json"
with open(theorems_file_path, 'r') as file:
    theorems = file.read()
PROMPT_PREFIX = "You are given available theorems, each can have more than one variation and it includes premise and conclusion. You will be given a problem with some assumptions and a conclusion to prove. You should fine the suitable theory in order to prove the conclusion. Available theorems:"

EXAMPLE_1_SUFFIX = "You are given that: ParallelBetweenLine(EF,GH) Collinear(EMF) Line(EF) Line(GH) Choose one theory out of the available theorems to prove: ParallelBetweenLine(EM,GH) Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_1_SUFFIX_NaturalLanguage = "You are given that: The lines EF and GH are parallel, and the points E, M, and F are collinear. EF and GH are individual lines. Choose one theory out of the available theorems to prove: The lines EM and GH are parallel. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_2_SUFFIX = "You are given that: PerpendicularBetweenLine(FE,GE) PerpendicularBetweenLine(EG,HG) Line(FE) Line(GE) Line(EG) Line(HG) Choose one theory out of the available theorems to prove: ParallelBetweenLine(EF,GH) Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_2_SUFFIX_NaturalLanguage = "You are given that: The lines FE and GE are perpendicular to each other, and similarly, the lines EG and HG are perpendicular to each other. FE, GE, EG, and HG are all individual lines. Choose one theory out of the available theorems to prove: The lines EF and GH are parallel. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_3_SUFFIX = "You are given that: Collinear(FOH) Angle(FOC) Angle(COH) Choose one theory out of the available theorems to prove: Equal(Add(MeasureOfAngle(FOC),MeasureOfAngle(COH)),180) Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_3_SUFFIX_NaturalLanguage = "You are given that: The points F, O, and H are collinear. There are angles formed at point O, specifically Angle FOC and Angle COH. Choose one theory out of the available theorems to prove: The sum of the measures of Angle FOC and Angle COH is equal to 180 degrees. Write only the name of theory with the correct parameters corresponding to our problem."


EXAMPLE_4_SUFFIX = "You are given that: Line(IK) Angle(HIJ) IsBisectorOfAngle(IK,HIJ) Equal(MeasureOfAngle(IJK),90) Equal(MeasureOfAngle(KHI),90) Choose one theory out of the available theorems to prove: Equal(LengthOfLine(KH),LengthOfLine(KJ)) Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_4_SUFFIX_NaturalLanguage = "You are given that: Line IK is the angle bisector of Angle HIJ. The measures of Angle IJK and Angle KHI are both equal to 90 degrees. Choose one theory out of the available theorems to prove: The length of line KH is equal to the length of line KJ. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_5_SUFFIX = "You are given that: Collinear(XYZ) Choose one theory out of the available theorems to prove: Equal(LengthOfLine(XZ),Add(LengthOfLine(XY),LengthOfLine(YZ))) Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_5_SUFFIX_NaturalLanguage = "You are given that: The points X, Y, and Z are collinear. Choose one theory out of the available theorems to prove: The length of line XZ is equal to the sum of the lengths of lines XY and YZ. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_6_SUFFIX = "You are given that: Collinear(LZM) Line(LZ) Line(ZM) Equal(LengthOfLine(LZ),LengthOfLine(ZM)). Choose one theory out of the available theorems to prove: IsMidpointOfLine(Z,LM). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_6_SUFFIX_NaturalLanguage = "You are given that: The points L, Z, and M are collinear. Lines LZ and ZM have equal lengths. Choose one theory out of the available theorems to prove: Point Z is the midpoint of line LM. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_7_SUFFIX = "You are given that: Angle(FBC) Angle(BDE) Collinear(FBD) Equal(MeasureOfAngle(FBC),MeasureOfAngle(BDE)). Choose one theory out of the available theorems to prove: ParallelBetweenLine(BC,DE). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_7_SUFFIX_NaturalLanguage = "You are given that: The points F, B, and D are collinear. The measure of Angle FBC is equal to the measure of Angle BDE. Choose one theory out of the available theorems to prove:The lines BC and DE are parallel to each other. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_8_SUFFIX = "You are given that: Angle(IHJ) Angle(HJK) Equal(Add(MeasureOfAngle(IHJ),MeasureOfAngle(HJK)),180). Choose one theory out of the available theorems to prove: ParallelBetweenLine(HI,JK). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_8_SUFFIX_NaturalLanguage = "You are given that: The sum of the measures of Angle IHJ and Angle HJK is equal to 180 degrees. Choose one theory out of the available theorems to prove: The lines HI and JK are parallel to each other. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_9_SUFFIX = "You are given that: Line(BC) Line(EF) ParallelBetweenLine(BC,EF) Collinear(QBE). Choose one theory out of the available theorems to prove: Equal(MeasureOfAngle(QBC),MeasureOfAngle(BEF)). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_9_SUFFIX_NaturalLanguage = "You are given that: The lines BC and EF are parallel to each other. The points Q, B, and E are collinear. Choose one theory out of the available theorems to prove: The measure of Angle QBC is equal to the measure of Angle BEF. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_10_SUFFIX = "You are given that: Polygon(BCD). Choose one theory out of the available theorems to prove:Equal(Mul(LengthOfLine(BC),Sin(MeasureOfAngle(BCD))),Mul(LengthOfLine(BD),Sin(MeasureOfAngle(CDB)))). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_10_SUFFIX_NaturalLanguage = "You are given that: BCD is a Polygon. Choose one theory out of the available theorems to prove: The product of the length of line BC and the sine of Angle BCD is equal to the product of the length of line BD and the sine of Angle CDB. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_11_SUFFIX = "You are given that: Polygon(ZYX) Collinear(ZWY) Collinear(ZQX) Line(ZW) Line(WY) Line(ZY) Line(ZQ) Line(ZX) Line(QX) Line(WQ) Equal(LengthOfLine(ZW),LengthOfLine(YW)) Equal(LengthOfLine(ZQ),LengthOfLine(XQ)). Choose one theory out of the available theorems to prove: IsMidsegmentOfTriangle(WQ,ZYX). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_11_SUFFIX_NaturalLanguage = "You are given that: ZYX is a Polygon. The points Z, W, and Y are collinear. The points Z, Q, and X are also collinear. The following are lines: ZW, WY, ZY, ZQ, ZX, QX, and WQ. The length of line ZW is equal to the length of line YW. The length of line ZQ is equal to the length of line XQ. Choose one theory out of the available theorems to prove: Line WQ is the midsegment of triangle ZYX. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_12_SUFFIX = "You are given that: Polygon(DEF) Line(DG) Line(GE) Line(DE) Line(FH) Line(HD) Line(FD) Collinear(DGE) Collinear(FHD) IsPerpendicularBisectorOfLine(OG,DE) IsPerpendicularBisectorOfLine(OH,FD). Choose one theory out of the available theorems to prove: IsCircumcenterOfTriangle(O,DEF). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_12_SUFFIX_NaturalLanguage = "You are given that:DEF is a polygon. The following lines exist: DG, GE, DE, FH, HD, and FD. The points D, G, and E are collinear. The points F, H, and D are also collinear. Line OG is the perpendicular bisector of line DE. Line OH is the perpendicular bisector of line FD. Choose one theory out of the available theorems to prove: Point O is the circumcenter of triangle DEF. Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_13_SUFFIX = "You are given that: Polygon(HIJ) Polygon(KLM) Equal(LengthOfLine(HI),LengthOfLine(KL)) Equal(LengthOfLine(IJ),LengthOfLine(LM)) Equal(LengthOfLine(JH),LengthOfLine(MK)). Choose one theory out of the available theorems to prove: CongruentBetweenTriangle(HIJ,KLM). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_13_SUFFIX_NaturalLanguage = "You are given that: HIJ is a polygon. KLM is a polygon. The length of line HI is equal to the length of line KL. The length of line IJ is equal to the length of line LM. The length of line JH is equal to the length of line MK. Choose one theory out of the available theorems to prove: CongruentBetweenTriangle(HIJ,KLM). Write only the name of theory with the correct parameters corresponding to our problem."

EXAMPLE_14_SUFFIX = "You are given that: Polygon(GHI) Polygon(JKL) Equal(LengthOfLine(GH),LengthOfLine(LJ)) Equal(LengthOfLine(GI),LengthOfLine(KL)) Equal(LengthOfLine(IG),LengthOfLine(JK)). Choose one theory out of the available theorems to prove: MirrorCongruentBetweenTriangle(GHI,JKL). Write only the name of theory with the correct parameters corresponding to our problem."
EXAMPLE_14_SUFFIX_NaturalLanguage = "You are given that: GHI is a polygon. JKL is a polygon. The length of line GH is equal to the length of line LJ. The length of line GI is equal to the length of line KL. The length of line IG is equal to the length of line JK. Choose one theory out of the available theorems to prove: Triangles GHI and JKL are mirror congruent. Write only the name of theory with the correct parameters corresponding to our problem."





EXAMPLE_1_GROUND_TRUTH = "parallel_property_collinear_extend(EF,GH,M)"
EXAMPLE_2_GROUND_TRUTH = "parallel_judgment_per_per(EF,GH)"
EXAMPLE_3_GROUND_TRUTH = "adjacent_complementary_angle(FOC,COH)"
EXAMPLE_4_GROUND_TRUTH = "bisector_of_angle_property_distance_equal(IK,HIJ)"
EXAMPLE_5_GROUND_TRUTH = "line_addition(XY,YZ)"
EXAMPLE_6_GROUND_TRUTH = "midpoint_of_line_judgment(Z,LM)"
EXAMPLE_7_GROUND_TRUTH = "parallel_judgment_corresponding_angle(BC,DE,F)"
EXAMPLE_8_GROUND_TRUTH = "parallel_judgment_ipsilateral_internal_angle(HI,JK)"
EXAMPLE_9_GROUND_TRUTH = "parallel_property_corresponding_angle(BC,EF,Q)"
EXAMPLE_10_GROUND_TRUTH = "sine_theorem(BCD)"

EXAMPLE_11_GROUND_TRUTH = "midsegment_of_triangle_judgment_midpoint(WQ,ZYX)"
EXAMPLE_12_GROUND_TRUTH = "circumcenter_of_triangle_judgment_intersection(O,DEF,G,H)"
EXAMPLE_13_GROUND_TRUTH = "congruent_triangle_judgment_sss(HIJ,KLM)"
EXAMPLE_14_GROUND_TRUTH = "mirror_congruent_triangle_judgment_sss(GHI,JKL)"


easy_examples = [EXAMPLE_1_SUFFIX, EXAMPLE_2_SUFFIX, EXAMPLE_3_SUFFIX, EXAMPLE_4_SUFFIX, EXAMPLE_5_SUFFIX, EXAMPLE_6_SUFFIX, EXAMPLE_7_SUFFIX, EXAMPLE_8_SUFFIX, EXAMPLE_9_SUFFIX, EXAMPLE_10_SUFFIX]
hard_examples = [EXAMPLE_11_SUFFIX, EXAMPLE_12_SUFFIX, EXAMPLE_13_SUFFIX, EXAMPLE_14_SUFFIX]
examples = easy_examples + hard_examples

easy_examples_NaturalLanguage = [EXAMPLE_1_SUFFIX_NaturalLanguage, EXAMPLE_2_SUFFIX_NaturalLanguage, EXAMPLE_3_SUFFIX_NaturalLanguage, EXAMPLE_4_SUFFIX_NaturalLanguage, EXAMPLE_5_SUFFIX_NaturalLanguage,
                            EXAMPLE_6_SUFFIX_NaturalLanguage, EXAMPLE_7_SUFFIX_NaturalLanguage, EXAMPLE_8_SUFFIX_NaturalLanguage, EXAMPLE_9_SUFFIX_NaturalLanguage, EXAMPLE_10_SUFFIX_NaturalLanguage]
hard_examples_NaturalLanguage = [EXAMPLE_11_SUFFIX_NaturalLanguage, EXAMPLE_12_SUFFIX_NaturalLanguage, EXAMPLE_13_SUFFIX_NaturalLanguage, EXAMPLE_14_SUFFIX_NaturalLanguage]
examples_NaturalLanguage = easy_examples_NaturalLanguage + hard_examples_NaturalLanguage


easy_gt = [EXAMPLE_1_GROUND_TRUTH, EXAMPLE_2_GROUND_TRUTH, EXAMPLE_3_GROUND_TRUTH, EXAMPLE_4_GROUND_TRUTH, EXAMPLE_5_GROUND_TRUTH, EXAMPLE_6_GROUND_TRUTH, EXAMPLE_7_GROUND_TRUTH, EXAMPLE_8_GROUND_TRUTH, EXAMPLE_9_GROUND_TRUTH, EXAMPLE_10_GROUND_TRUTH]
hard_gt = [EXAMPLE_11_GROUND_TRUTH, EXAMPLE_12_GROUND_TRUTH, EXAMPLE_13_GROUND_TRUTH, EXAMPLE_14_GROUND_TRUTH]
gt = easy_gt + hard_gt

def call_gpt(model, messages, temperature=0, wait_time=1, retry_wait_time=6, max_retries=10):
    retries = 0
    while retries <= max_retries:
        try:
            response = openai.ChatCompletion.create(
                model=model,
                messages=messages,
                max_tokens=4096,
                temperature=temperature,
                top_p=1,
                frequency_penalty=0,
                presence_penalty=0,
            )

            if response and response.choices and response.choices[0]:
                res = response.choices[0].message['content'].strip()
                time.sleep(wait_time)
                return res

        except openai.error.OpenAIError as e:
            print(f"OpenAIError: {e}. Retrying in {retry_wait_time} seconds...")
            time.sleep(retry_wait_time)
            retries += 1
            if retries > max_retries:
                print("Failed after maximum retries.")
                raise Exception(f"Failed after {max_retries} attempts due to OpenAI errors.")
        except Exception as e:
            print(f"Unexpected error: {e}. Not retrying.")
            raise Exception(f"Unexpected error: {e}")

def gpt_response(messages, model_name):
    resp = call_gpt(model=model_name, messages=messages)
    return resp


def run_example(prompt_suffix, model_name):
    prompt = PROMPT_PREFIX + "\n" + theorems + "\n" + prompt_suffix
    initial_message = {
        "role": "user",
        "content": prompt
    }
    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        initial_message
    ]

    resp = gpt_response(messages, model_name)
    return resp



def run_multiple_times(examples, gt, model_name, num_runs):
    correct_theorems_list = []
    correct_theorems_w_params_list = []

    for _ in range(num_runs):
        count_correct_theorems = 0
        count_correct_theorems_w_params = 0

        for i in range(len(examples)):
            example = examples[i]
            ground_truth = gt[i]
            resp = run_example(example, model_name)

            if ground_truth in resp:
                count_correct_theorems_w_params += 1
                count_correct_theorems += 1
            elif ground_truth.split("(")[0] in resp:
                count_correct_theorems += 1

        correct_theorems_list.append(count_correct_theorems / len(examples))
        correct_theorems_w_params_list.append(count_correct_theorems_w_params / len(examples))

    correct_theorems_mean = np.mean(correct_theorems_list)
    correct_theorems_std = np.std(correct_theorems_list)
    correct_theorems_w_params_mean = np.mean(correct_theorems_w_params_list)
    correct_theorems_w_params_std = np.std(correct_theorems_w_params_list)

    print(f"After {num_runs} runs, each run on the same {len(examples)} examples:")
    print(f"Model: {model_name}")
    print(f"Correct theorems mean: {correct_theorems_mean:.2f} (+- {correct_theorems_std:.2f})")
    print(f"Correct theorems with parameters mean: {correct_theorems_w_params_mean:.2f} (+- {correct_theorems_w_params_std:.2f})")

    # print(f"Correct theorems mean: {correct_theorems_mean:.2f}")
    # print(f"Correct theorems std: {correct_theorems_std:.2f}")
    # print(f"Correct theorems with parameters mean: {correct_theorems_w_params_mean:.2f}")
    # print(f"Correct theorems with parameters std: {correct_theorems_w_params_std:.2f}")


run_multiple_times(hard_examples_NaturalLanguage, hard_gt, model_name="gpt-4o", num_runs=10)



