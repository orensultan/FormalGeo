import time
import openai
import json

import numpy as np

openai.api_key = "sk-svcacct-kVTUGOlCTL2vge6gtHi--la5vr8g-lqT3ieuWGdHQBrYChItgkm2k1WPS9mA-MXe7ebaPHCMk8YrCft1OT3BlbkFJLNl-eYBXpQiokB5m3Nw0oiO9ZOe_Paf1WH0Kh4If52-rQ92DiSodgoopxiDoQDKlAGYDPRpiWamueq8vQA"
theorems_file_path = "formalgeo7k_v1/gdl/theorem_GDL.json"
with open(theorems_file_path, 'r') as file:
    theorems = file.read()
PROMPT_PREFIX = "You are given available theorems, each can have more than one variation and it includes premise and conclusion. You will be given a problem in geometry (PROBLEM) with some premise and a conclusion to prove (CONCLUSION_TO_PROVE). You should choose the correct theorem in order to prove the conclusion. Your task is to write only the name of theorem with the correct parameters corresponding to our problem without spaces between the arguments (THEOREM_CALL)\n Available theorems:" + "\n" + theorems + "\nInputs: PROBLEM, CONCLUSION_TO_PROVE\nOutputs: THEOREM_CALL"

EXAMPLE_1_SUFFIX = "Problem:\nLine(EF) Line(GH) ParallelBetweenLine(EF,GH) Collinear(EMF).\nCONCLUSION_TO_PROVE:\nParallelBetweenLine(EM,GH).\nOutputs:\nTHEOREM_CALL:\n" + "parallel_property_collinear_extend(EF,GH,M)"
EXAMPLE_1_SUFFIX_NaturalLanguage = "Problem:\nThe lines EF and GH are parallel, and the points E, M, and F are collinear. EF and GH are individual lines.\nCONCLUSION_TO_PROVE:\nThe lines EM and GH are parallel.\nOutputs:\nTHEOREM_CALL:\n" + "parallel_property_collinear_extend(EF,GH,M)"
PROMPT = PROMPT_PREFIX + "\n" + EXAMPLE_1_SUFFIX + "\nInputs:"

EXAMPLE_2_SUFFIX = "Problem:\nLine(FE) Line(GE) Line(EG) Line(HG) PerpendicularBetweenLine(FE,GE) PerpendicularBetweenLine(EG,HG).\nCONCLUSION_TO_PROVE:\nParallelBetweenLine(EF,GH)."
EXAMPLE_2_SUFFIX_NaturalLanguage = "Problem:\nThe lines FE and GE are perpendicular to each other, and similarly, the lines EG and HG are perpendicular to each other.\nCONCLUSION_TO_PROVE:\nThe lines EF and GH are parallel."

EXAMPLE_3_SUFFIX = "Problem:\nAngle(FOC) Angle(COH) Collinear(FOH).\nCONCLUSION_TO_PROVE:\nEqual(Add(MeasureOfAngle(FOC),MeasureOfAngle(COH)),180). "
EXAMPLE_3_SUFFIX_NaturalLanguage = "Problem:\nThere are angles formed at point O, specifically Angle FOC and Angle COH. The points F, O, and H are collinear.\nCONCLUSION_TO_PROVE:\nThe sum of the measures of Angle FOC and Angle COH is equal to 180 degrees."


EXAMPLE_4_SUFFIX = "Problem:\nLine(IK) Angle(HIJ) Equal(MeasureOfAngle(IJK),90) IsBisectorOfAngle(IK,HIJ) Equal(MeasureOfAngle(KHI),90).\nCONCLUSION_TO_PROVE:\nEqual(LengthOfLine(KH),LengthOfLine(KJ))."
EXAMPLE_4_SUFFIX_NaturalLanguage = "Problem:\nLine IK is the angle bisector of Angle HIJ. The measures of Angle IJK and Angle KHI are both equal to 90 degrees.\nCONCLUSION_TO_PROVE:\nThe length of line KH is equal to the length of line KJ."

EXAMPLE_5_SUFFIX = "Problem:\nCollinear(XYZ).\nCONCLUSION_TO_PROVE:\nEqual(LengthOfLine(XZ),Add(LengthOfLine(XY),LengthOfLine(YZ)))."
EXAMPLE_5_SUFFIX_NaturalLanguage = "Problem:\nThe points X, Y, and Z are collinear.\nCONCLUSION_TO_PROVE:\nThe length of line XZ is equal to the sum of the lengths of lines XY and YZ."


EXAMPLE_6_SUFFIX = "Problem:\nLine(LZ) Line(ZM) Collinear(LZM) Equal(LengthOfLine(LZ),LengthOfLine(ZM)).\nCONCLUSION_TO_PROVE:\nIsMidpointOfLine(Z,LM)."
EXAMPLE_6_SUFFIX_NaturalLanguage = "Problem:\nLines LZ and ZM have equal lengths. The points L, Z, and M are collinear.\nCONCLUSION_TO_PROVE:\nPoint Z is the midpoint of line LM."


EXAMPLE_7_SUFFIX = "Problem:\nAngle(FBC) Angle(BDE) Equal(MeasureOfAngle(FBC),MeasureOfAngle(BDE)) Collinear(FBD).\nCONCLUSION_TO_PROVE:\nParallelBetweenLine(BC,DE)."
EXAMPLE_7_SUFFIX_NaturalLanguage = "Problem:\nThe measure of Angle FBC is equal to the measure of Angle BDE. The points F, B, and D are collinear.\nCONCLUSION_TO_PROVE:\nthe lines BC and DE are parallel to each other."


EXAMPLE_8_SUFFIX = "Problem:\nEqual(Add(MeasureOfAngle(IHJ),MeasureOfAngle(HJK)),180) Angle(IHJ) Angle(HJK).\nCONCLUSION_TO_PROVE:\nParallelBetweenLine(HI,JK)."
EXAMPLE_8_SUFFIX_NaturalLanguage = "Problem:\nThe sum of the measures of Angle IHJ and Angle HJK is equal to 180 degrees.\nCONCLUSION_TO_PROVE:\nThe lines HI and JK are parallel to each other."



EXAMPLE_9_SUFFIX = "Problem:\nLine(BC) Line(EF) Collinear(QBE) ParallelBetweenLine(BC,EF).\nCONCLUSION_TO_PROVE:\nEqual(MeasureOfAngle(QBC),MeasureOfAngle(BEF))."
EXAMPLE_9_SUFFIX_NaturalLanguage = "Problem:\nThe points Q, B, and E are collinear The lines BC and EF are parallel to each other.\nCONCLUSION_TO_PROVE:\nThe measure of Angle QBC is equal to the measure of Angle BEF."


EXAMPLE_10_SUFFIX = "Problem:\nPolygon(BCD).\nCONCLUSION_TO_PROVE:\nEqual(Mul(LengthOfLine(BC),Sin(MeasureOfAngle(BCD))),Mul(LengthOfLine(BD),Sin(MeasureOfAngle(CDB))))."
EXAMPLE_10_SUFFIX_NaturalLanguage = "Problem:\nBCD is a Polygon.\nCONCLUSION_TO_PROVE:\nThe product of the length of line BC and the sine of Angle BCD is equal to the product of the length of line BD and the sine of Angle CDB."


EXAMPLE_11_SUFFIX = "Problem:\nPolygon(ZYX) Line(ZW) Line(WY) Line(ZY) Line(ZQ) Line(ZX) Line(QX) Line(WQ) Collinear(ZWY) Collinear(ZQX) Equal(LengthOfLine(ZW),LengthOfLine(YW)) Equal(LengthOfLine(ZQ),LengthOfLine(XQ)).\nCONCLUSION_TO_PROVE:\nIsMidsegmentOfTriangle(WQ,ZYX)."
EXAMPLE_11_SUFFIX_NaturalLanguage = "Problem:\nZYX is a Polygon. The following are lines: ZW, WY, ZY, ZQ, ZX, QX, and WQ. The points Z, W, and Y are collinear. The points Z, Q, and X are also collinear. The length of line ZW is equal to the length of line YW. The length of line ZQ is equal to the length of line XQ.\nCONCLUSION_TO_PROVE:\nLine WQ is the midsegment of triangle ZYX."


EXAMPLE_12_SUFFIX = "Problem:\nPolygon(HIJ) Polygon(KLM) Equal(LengthOfLine(HI),LengthOfLine(KL)) Equal(LengthOfLine(IJ),LengthOfLine(LM)) Equal(LengthOfLine(JH),LengthOfLine(MK)).\nCONCLUSION_TO_PROVE:\nCongruentBetweenTriangle(HIJ,KLM)."
EXAMPLE_12_SUFFIX_NaturalLanguage = "Problem:\nHIJ is a polygon. KLM is a polygon. The length of line HI is equal to the length of line KL. The length of line IJ is equal to the length of line LM. The length of line JH is equal to the length of line MK.\nCONCLUSION_TO_PROVE:\nCongruentBetweenTriangle(HIJ,KLM)."


EXAMPLE_13_SUFFIX = "Problem:\nPolygon(GHI) Polygon(JKL) Equal(LengthOfLine(GH),LengthOfLine(LJ)) Equal(LengthOfLine(GI),LengthOfLine(KL)) Equal(LengthOfLine(IG),LengthOfLine(JK)).\nCONCLUSION_TO_PROVE:\nMirrorCongruentBetweenTriangle(GHI,JKL)."
EXAMPLE_13_SUFFIX_NaturalLanguage = "Problem:\nGHI is a polygon. JKL is a polygon. The length of line GH is equal to the length of line LJ. The length of line GI is equal to the length of line KL. The length of line IG is equal to the length of line JK.\nCONCLUSION_TO_PROVE:\nTriangles GHI and JKL are mirror congruent."


EXAMPLE_14_SUFFIX = "Problem:\nPolygon(BCD) Polygon(EFG) Equal(MeasureOfAngle(BCD),90) Equal(MeasureOfAngle(GFE),90) Equal(LengthOfLine(BD),LengthOfLine(EF)) (Equal(LengthOfLine(CD),LengthOfLine(FG)) Equal(LengthOfLine(BC),LengthOfLine(EG))).\nCONCLUSION_TO_PROVE:\nMirrorCongruentBetweenTriangle(BCD,EFG)."
EXAMPLE_14_SUFFIX_NaturalLanguage = "Problem:\nBCD is a polygon. EFG is a polygon. The measure of Angle BCD is 90 degrees. The measure of Angle GFE is 90 degrees. The length of line BD is equal to the length of line EF. Additionally, either the length of line CD is equal to the length of line FG, or the length of line BC is equal to the length of line EG.\nCONCLUSION_TO_PROVE:\nTriangles BCD and EFG are mirror congruent."


EXAMPLE_15_SUFFIX = "Problem:\nPolygon(HEF) Collinear(EOF) Line(HO) Equal(LengthOfLine(EO),LengthOfLine(FO)).\nCONCLUSION_TO_PROVE:\nIsMedianOfTriangle(HO,HEF)."
EXAMPLE_15_SUFFIX_NaturalLanguage = "Problem:\nHEF is a polygon. The points E, O, and F are collinear. Line HO exists, and the lengths of line segments EO and FO are equal.\nCONCLUSION_TO_PROVE:\nThe line segment HO is the median of triangle HEF."


EXAMPLE_16_SUFFIX = "Problem:\nAngle(CDA) Angle(ADB) Equal(MeasureOfAngle(CDA),MeasureOfAngle(ADB)).\nCONCLUSION_TO_PROVE:\nIsBisectorOfAngle(DA,CDB)."
EXAMPLE_16_SUFFIX_NaturalLanguage = "Problem:\nThe angles CDA and ADB are equal in measure.\nCONCLUSION_TO_PROVE:\nThe line segment DA is the bisector of angle CDB."


EXAMPLE_17_SUFFIX = "Problem:\nAngle(CBA) Angle(DAB) Equal(MeasureOfAngle(CBA),MeasureOfAngle(DAB)).\nCONCLUSION_TO_PROVE:\nParallelBetweenLine(BC,DA)."
EXAMPLE_17_SUFFIX_NaturalLanguage = "Problem:\nThe measure of angle CBA is equal to the measure of angle DAB.\nCONCLUSION_TO_PROVE:\nLine BC is parallel to line DA."


EXAMPLE_18_SUFFIX = "Problem:\nParallelBetweenLine(DC,BA) PerpendicularBetweenLine(CD,BD).\nCONCLUSION_TO_PROVE:\nPerpendicularBetweenLine(DB,AB)."
EXAMPLE_18_SUFFIX_NaturalLanguage = "Problem:\nLine DC is parallel to line BA, and line CD is perpendicular to line BD.\nCONCLUSION_TO_PROVE:\nLine DB is perpendicular to line AB."


EXAMPLE_19_SUFFIX = "Problem:\nPolygon(CBA) Polygon(FED) Equal(LengthOfLine(CB),LengthOfLine(FE)) Equal(MeasureOfAngle(ACB),MeasureOfAngle(DFE)) Equal(LengthOfLine(CA),LengthOfLine(FD)).\nCONCLUSION_TO_PROVE:\nCongruentBetweenTriangle(CBA,FED)."
EXAMPLE_19_SUFFIX_NaturalLanguage = "Problem:\nThe polygons CBA and FED have the following properties: the length of line CB is equal to the length of line FE, the measure of angle ACB is equal to the measure of angle DFE, and the length of line CA is equal to the length of line FD.\nCONCLUSION_TO_PROVE:\nThe triangles CBA and FED are congruent."


EXAMPLE_20_SUFFIX = "Problem:\nIsMedianOfTriangle(DZ,DEF) IsoscelesTriangle(DEF).\nCONCLUSION_TO_PROVE:\nIsBisectorOfAngle(DZ,FDE)."
EXAMPLE_20_SUFFIX_NaturalLanguage = "Problem:\nDZ is the median of triangle DEF, and triangle DEF is isosceles.\nCONCLUSION_TO_PROVE:\nDZ is the bisector of angle FDE."


EXAMPLE_21_SUFFIX = "Problem:\n(Parallelogram(BCDE) or Trapezoid(BCDE)) and (Line(BD) and Equal(MeasureOfAngle(CDB),90)).\nCONCLUSION_TO_PROVE:\nIsAltitudeOfQuadrilateral(BD,BCDE)."
EXAMPLE_21_SUFFIX_NaturalLanguage = "Problem:\nA parallelogram BCDE or trapezoid BCDE exists, and line BD is drawn, with the measure of angle CDB being equal to 90 degrees.\nCONCLUSION_TO_PROVE:\n whether line BD is the altitude of quadrilateral BCDE."


EXAMPLE_22_SUFFIX = "Problem:\nCollinear(MQN) and Line(LQ) and Equal(MeasureOfAngle(MQL),90) and (Parallelogram(LMNO) or Trapezoid(LMNO)).\nCONCLUSION_TO_PROVE:\nIsAltitudeOfQuadrilateral(LQ,LMNO)."
EXAMPLE_22_SUFFIX_NaturalLanguage = "Problem:\nPoints M, Q, and N are collinear, and line LQ is drawn. The measure of angle MQL is 90 degrees. Additionally, quadrilateral LMNO is either a parallelogram or a trapezoid.\nCONCLUSION_TO_PROVE:\nline LQ is the altitude of quadrilateral LMNO."


EXAMPLE_23_SUFFIX = "Problem:\nCollinear(XOD) Collinear(YDZ) IsOrthocenterOfTriangle(O,XYZ).\nCONCLUSION_TO_PROVE:\nIsAltitudeOfTriangle(XD,XYZ)."
EXAMPLE_23_SUFFIX_NaturalLanguage = "Problem:\nPoints X, O, and D are collinear, and points Y, D, and Z are collinear. O is the orthocenter of triangle XYZ.\nCONCLUSION_TO_PROVE:\nline XD is the altitude of triangle XYZ."


EXAMPLE_24_SUFFIX = "Problem:\nMirrorCongruentBetweenTriangle(BCD,EFG).\nCONCLUSION_TO_PROVE:\nEqual(AreaOfTriangle(BCD),AreaOfTriangle(EFG))."
EXAMPLE_24_SUFFIX_NaturalLanguage = "Problem:\nThe triangles BCD and EFG are mirror congruent.\nCONCLUSION_TO_PROVE:\the area of triangle BCD is equal to the area of triangle EFG."


EXAMPLE_25_SUFFIX = "Problem:\nLine(WY) Line(XZ) Parallelogram(WXYZ) Equal(LengthOfLine(WY),LengthOfLine(XY)).\nCONCLUSION_TO_PROVE:\nRectangle(WXYZ)."
EXAMPLE_25_SUFFIX_NaturalLanguage = "Problem:\nThere are two lines, WY and XZ, and WXYZ forms a parallelogram. Additionally, the length of line WY is equal to the length of line XY.\nCONCLUSION_TO_PROVE:\nWXYZ is a rectangle."








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
EXAMPLE_12_GROUND_TRUTH = "congruent_triangle_judgment_sss(HIJ,KLM)"
EXAMPLE_13_GROUND_TRUTH = "mirror_congruent_triangle_judgment_sss(GHI,JKL)"
EXAMPLE_14_GROUND_TRUTH = "mirror_congruent_triangle_judgment_hl(BCD,EFG)"
EXAMPLE_15_GROUND_TRUTH = "median_of_triangle_judgment(HO,HEF)"
EXAMPLE_16_GROUND_TRUTH = "bisector_of_angle_judgment_angle_equal(DA,CDB)"
EXAMPLE_17_GROUND_TRUTH = "parallel_judgment_alternate_interior_angle(BC,DA)"
EXAMPLE_18_GROUND_TRUTH = "parallel_property_par_per(DC,BA)"
EXAMPLE_19_GROUND_TRUTH = "congruent_triangle_judgment_sas(CBA,FED)"
EXAMPLE_20_GROUND_TRUTH = "isosceles_triangle_property_line_coincidence(DEF,Z)"
EXAMPLE_21_GROUND_TRUTH = "altitude_of_quadrilateral_judgment_diagonal(BCDE)"
EXAMPLE_22_GROUND_TRUTH = "altitude_of_quadrilateral_judgment_left_vertex(LQ,LMNO)"
EXAMPLE_23_GROUND_TRUTH = "orthocenter_of_triangle_property_intersection(O,XYZ,D)"
EXAMPLE_24_GROUND_TRUTH = "mirror_congruent_triangle_property_area_equal(BCD,EFG)"
EXAMPLE_25_GROUND_TRUTH = "rectangle_judgment_diagonal_equal(WXYZ)"



examples = [EXAMPLE_2_SUFFIX, EXAMPLE_3_SUFFIX, EXAMPLE_4_SUFFIX, EXAMPLE_5_SUFFIX, EXAMPLE_6_SUFFIX, EXAMPLE_7_SUFFIX, EXAMPLE_8_SUFFIX, EXAMPLE_9_SUFFIX, EXAMPLE_10_SUFFIX, EXAMPLE_11_SUFFIX, EXAMPLE_12_SUFFIX, EXAMPLE_13_SUFFIX, EXAMPLE_14_SUFFIX, EXAMPLE_15_SUFFIX, EXAMPLE_16_SUFFIX, EXAMPLE_17_SUFFIX, EXAMPLE_18_SUFFIX, EXAMPLE_19_SUFFIX, EXAMPLE_20_SUFFIX, EXAMPLE_21_SUFFIX, EXAMPLE_22_SUFFIX, EXAMPLE_23_SUFFIX, EXAMPLE_24_SUFFIX, EXAMPLE_25_SUFFIX]

examples_NaturalLanguage = [EXAMPLE_2_SUFFIX_NaturalLanguage, EXAMPLE_3_SUFFIX_NaturalLanguage, EXAMPLE_4_SUFFIX_NaturalLanguage, EXAMPLE_5_SUFFIX_NaturalLanguage, EXAMPLE_6_SUFFIX_NaturalLanguage, EXAMPLE_7_SUFFIX_NaturalLanguage, EXAMPLE_8_SUFFIX_NaturalLanguage, EXAMPLE_9_SUFFIX_NaturalLanguage, EXAMPLE_10_SUFFIX_NaturalLanguage, EXAMPLE_11_SUFFIX_NaturalLanguage, EXAMPLE_12_SUFFIX_NaturalLanguage, EXAMPLE_13_SUFFIX_NaturalLanguage, EXAMPLE_14_SUFFIX_NaturalLanguage, EXAMPLE_15_SUFFIX_NaturalLanguage, EXAMPLE_16_SUFFIX_NaturalLanguage, EXAMPLE_17_SUFFIX_NaturalLanguage, EXAMPLE_18_SUFFIX_NaturalLanguage, EXAMPLE_19_SUFFIX_NaturalLanguage, EXAMPLE_20_SUFFIX_NaturalLanguage,  EXAMPLE_21_SUFFIX_NaturalLanguage, EXAMPLE_22_SUFFIX_NaturalLanguage, EXAMPLE_23_SUFFIX_NaturalLanguage, EXAMPLE_24_SUFFIX_NaturalLanguage, EXAMPLE_25_SUFFIX_NaturalLanguage]

gt = [EXAMPLE_2_GROUND_TRUTH, EXAMPLE_3_GROUND_TRUTH, EXAMPLE_4_GROUND_TRUTH, EXAMPLE_5_GROUND_TRUTH, EXAMPLE_6_GROUND_TRUTH, EXAMPLE_7_GROUND_TRUTH, EXAMPLE_8_GROUND_TRUTH, EXAMPLE_9_GROUND_TRUTH, EXAMPLE_10_GROUND_TRUTH, EXAMPLE_11_GROUND_TRUTH, EXAMPLE_12_GROUND_TRUTH, EXAMPLE_13_GROUND_TRUTH, EXAMPLE_14_GROUND_TRUTH, EXAMPLE_15_GROUND_TRUTH, EXAMPLE_16_GROUND_TRUTH, EXAMPLE_17_GROUND_TRUTH, EXAMPLE_18_GROUND_TRUTH, EXAMPLE_19_GROUND_TRUTH, EXAMPLE_20_GROUND_TRUTH, EXAMPLE_21_GROUND_TRUTH, EXAMPLE_22_GROUND_TRUTH, EXAMPLE_23_GROUND_TRUTH, EXAMPLE_24_GROUND_TRUTH, EXAMPLE_25_GROUND_TRUTH]


# def call_gpt(model, messages, temperature=0, wait_time=1, retry_wait_time=6, max_retries=10):
#     retries = 0
#     while retries <= max_retries:
#         try:
#             response = openai.ChatCompletion.create(
#                 model=model,
#                 messages=messages,
#                 max_tokens=4096,
#                 temperature=temperature,
#                 top_p=1,
#                 frequency_penalty=0,
#                 presence_penalty=0,
#             )
#
#             if response and response.choices and response.choices[0]:
#                 res = response.choices[0].message['content'].strip()
#                 time.sleep(wait_time)
#                 return res
#
#         except openai.error.OpenAIError as e:
#             print(f"OpenAIError: {e}. Retrying in {retry_wait_time} seconds...")
#             time.sleep(retry_wait_time)
#             retries += 1
#             if retries > max_retries:
#                 print("Failed after maximum retries.")
#                 raise Exception(f"Failed after {max_retries} attempts due to OpenAI errors.")
#         except Exception as e:
#             print(f"Unexpected error: {e}. Not retrying.")
#             raise Exception(f"Unexpected error: {e}")


def call_gpt(model, messages, temperature=1, wait_time=1, retry_wait_time=6, max_retries=10):
    # Filter out messages with 'system' role
    filtered_messages = [msg for msg in messages if msg['role'] != 'system']

    retries = 0
    while retries <= max_retries:
        try:
            response = openai.ChatCompletion.create(
                model=model,
                messages=filtered_messages,
                max_completion_tokens=4096,
                temperature=temperature,  # Default to 1 if the model only supports the default value
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
#
# def call_gpt(model, messages, wait_time=1, retry_wait_time=6, max_retries=10):
#     retries = 0
#
#     # Filter out 'system' role if the model doesn't support it
#     adjusted_messages = [msg for msg in messages if msg["role"] != "system"]
#
#     while retries <= max_retries:
#         try:
#             # Make the API request without temperature, since only default is supported
#             response = openai.ChatCompletion.create(
#                 model=model,
#                 messages=adjusted_messages,  # Use adjusted messages without 'system'
#                 max_completion_tokens=4096,  # Use max_completion_tokens instead of max_tokens
#                 top_p=1,
#                 frequency_penalty=0,
#                 presence_penalty=0,
#             )
#
#             # Extract the content from the response
#             if response and response.choices and response.choices[0]['message']['content']:
#                 res = response.choices[0]['message']['content'].strip()
#                 time.sleep(wait_time)
#                 return res
#
#         # Handle specific OpenAI API errors
#         except openai.error.OpenAIError as e:
#             print(f"OpenAIError: {e}. Retrying in {retry_wait_time} seconds...")
#             time.sleep(retry_wait_time)
#             retries += 1
#             if retries > max_retries:
#                 print("Failed after maximum retries.")
#                 raise Exception(f"Failed after {max_retries} attempts due to OpenAI errors.")
#
#         # Handle any other general exceptions
#         except Exception as e:
#             print(f"Unexpected error: {e}. Not retrying.")
#             raise Exception(f"Unexpected error: {e}")
#
#     return None  # Return None if max retries exceeded


def gpt_response(messages, model_name):
    resp = call_gpt(model=model_name, messages=messages)
    return resp


def run_example(prompt_suffix, model_name):
    prompt = PROMPT + "\n" + prompt_suffix + "\nOutputs:\nTHEOREM_CALL:\n"
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

    for run_id in range(num_runs):
        count_correct_theorems = 0
        count_correct_theorems_w_params = 0

        for i in range(len(examples)):
            example = examples[i]
            ground_truth = gt[i]
            resp = run_example(example, model_name)
            print("Run " + str(run_id+1))
            print("Example " + str(i+1) + ":\n" + example)
            print("Ground truth: " + ground_truth)
            print("Model response: " + resp)

            if ground_truth in resp:
                count_correct_theorems_w_params += 1
                count_correct_theorems += 1
                print("+1 correct theorems. +1 correct theorems with params")
            elif ground_truth.split("(")[0] in resp:
                count_correct_theorems += 1
                print("+1 correct theorems")

        ratio_correct_theorems = count_correct_theorems / len(examples)
        ratio_correct_theorems_w_params = count_correct_theorems_w_params / len(examples)
        print("Correct theorems for run " + str(run_id+1) + ": " + str(ratio_correct_theorems))
        print("Correct theorems with params for run " + str(run_id+1) + ": " + str(ratio_correct_theorems_w_params))
        correct_theorems_list.append(ratio_correct_theorems)
        correct_theorems_w_params_list.append(ratio_correct_theorems_w_params)

        print()

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


model_name = 'gpt-4o'

run_multiple_times(examples, gt, model_name=model_name, num_runs=1)



