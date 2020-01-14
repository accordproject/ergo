(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import String.

Require Import Qcert.Utils.Utils.
Require Import Qcert.Utils.OptimizerLogger.
Require Import Qcert.JSON.JSONSystem.
Require Import Qcert.EJson.EJsonSystem.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.Translation.Model.ForeignDataToEJson.
Require Import Qcert.Translation.Model.ForeignEJsonToJSON.
Require Import Qcert.Translation.Model.ForeignTypeToJSON.
Require Import Qcert.Translation.Operators.ForeignToJava.
Require Import Qcert.Translation.Operators.ForeignToJavaScriptAst.
Require Import Qcert.Translation.Operators.ForeignToScala.
Require Import Qcert.Translation.Operators.ForeignToEJsonRuntime.
Require Import Qcert.Translation.Operators.ForeignToSpark.
Require Import Qcert.Translation.Operators.ForeignToReduceOps.
Require Import Qcert.NNRCMR.Lang.ForeignReduceOps.
Require Import Qcert.NNRCMR.Lang.NNRCMR.
Require Import Qcert.cNRAEnv.Lang.cNRAEnv.
Require Import Qcert.NRAEnv.Lang.NRAEnv.
Require Import Qcert.cNNRC.Lang.cNNRC.
Require Import Qcert.NNRSimp.Lang.NNRSimp.
Require Import Qcert.DNNRC.Lang.DNNRCBase.
Require Import Qcert.tDNNRC.Lang.tDNNRC.
Require Import Qcert.Dataframe.Lang.Dataframe.
Require Import Qcert.Compiler.Model.CompilerRuntime.
Require Import Qcert.Compiler.Model.CompilerModel.

Require Import Qcert.Compiler.Component.LoggerComponent.
Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

(* XXX Export those for convenience *)
Require Export QcertData.
Require Export QcertEJson.
Require Export QcertDataToEJson.
Require Export QcertEJsonToJSON.
Require Export QcertToJava.
Require Export QcertToJavascriptAst.
Require Export QcertReduceOps.
Require Export QcertToReduceOps.
Require Export QcertToSpark.
Require Export QcertType.
Require Export QcertRuntime.
Require Export QcertToScala.
Require Export QcertDataTyping.
Require Export QcertTypeToJSON.
Require Export QcertTyping.

Instance enhanced_basic_model {model:brand_model} :
  basic_model
  := mk_basic_model
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_typing.

Module EnhancedForeignType <: CompilerForeignType.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
End EnhancedForeignType.

Module EnhancedModel(bm:CompilerBrandModel(EnhancedForeignType)) <: CompilerModel.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_basic_model : @basic_model
    := @enhanced_basic_model bm.compiler_brand_model.
  Definition compiler_model_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_model_foreign_ejson : foreign_ejson
    := enhanced_foreign_ejson.
  Definition compiler_model_foreign_to_ejson : foreign_to_ejson
    := enhanced_foreign_to_ejson.
  Definition compiler_model_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := enhanced_foreign_to_ejson_runtime.
  Definition compiler_model_foreign_to_json : foreign_to_json
    := enhanced_foreign_to_json.
  Definition compiler_model_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_model_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := enhanced_foreign_ejson_to_ajavascript.
  Definition compiler_model_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_model_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_model_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_model_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_model_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedModel.

Module CompEnhanced.
  Module Enhanced.
    Module Model.
      Definition basic_model (bm:brand_model) : basic_model
        := @enhanced_basic_model bm.
      
      Definition foreign_type : foreign_type
        := enhanced_foreign_type.
      
      Definition foreign_typing (bm:brand_model) : foreign_typing
        := @enhanced_foreign_typing bm.
      
    End Model.
    
    Module Data.
      (* intended for generated coq code, to stand out and be more
         easily distinguished from variables (hackily distinguished
         that is) *)

      Definition ddate_time (d:DATE_TIME) : data
        := dforeign (enhanceddateTime d).
      
      Definition ddate_time_duration (d:DATE_TIME_DURATION) : data
        := dforeign (enhanceddateTimeduration d).
      
      Definition ddate_time_period (d:DATE_TIME_PERIOD) : data
        := dforeign (enhanceddateTimeperiod d).
      
    End Data.
    
    Module Ops.
      Module Unary.
        Definition date_time_get_seconds
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_seconds).
        Definition date_time_get_minutes
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_minutes).
        Definition date_time_get_hours
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_hours).
        Definition date_time_get_days
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_days).
        Definition date_time_get_weeks
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_weeks).
        Definition date_time_get_months
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_months).
        Definition date_time_get_quarters
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_quarters).
        Definition date_time_get_years
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_get_years).
        Definition date_time_start_of_day
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_start_of_day).
        Definition date_time_start_of_week
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_start_of_week).
        Definition date_time_start_of_month
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_start_of_month).
        Definition date_time_start_of_quarter
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_start_of_quarter).
        Definition date_time_start_of_year
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_start_of_year).
        Definition date_time_end_of_day
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_end_of_day).
        Definition date_time_end_of_week
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_end_of_week).
        Definition date_time_end_of_month
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_end_of_month).
        Definition date_time_end_of_quarter
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_end_of_quarter).
        Definition date_time_end_of_year
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_end_of_year).
        Definition date_time_format_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_format_from_string).
        Definition date_time_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_from_string).
        Definition date_time_min
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_min).
        Definition date_time_max
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_max).
        Definition date_time_duration_amount
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_amount).
        Definition date_time_duration_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_string).
        Definition date_time_duration_from_seconds
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_seconds).
        Definition date_time_duration_from_minutes
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_minutes).
        Definition date_time_duration_from_hours
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_hours).
        Definition date_time_duration_from_days
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_days).
        Definition date_time_duration_from_weeks
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_weeks).
        Definition date_time_period_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_string).
        Definition date_time_period_from_days
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_days).
        Definition date_time_period_from_weeks
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_weeks).
        Definition date_time_period_from_months
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_months).
        Definition date_time_period_from_quarters
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_quarters).
        Definition date_time_period_from_years
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_period_from_years).

        (* for coq style syntax *)
        Definition OpDateTimeGetSeconds := date_time_get_seconds.
        Definition OpDateTimeGetMinutes := date_time_get_minutes.
        Definition OpDateTimeGetHours := date_time_get_hours.
        Definition OpDateTimeGetDays := date_time_get_days.
        Definition OpDateTimeGetWeeks := date_time_get_weeks.
        Definition OpDateTimeGetMonths := date_time_get_months.
        Definition OpDateTimeGetQuarters := date_time_get_quarters.
        Definition OpDateTimeGetYears := date_time_get_years.
        Definition OpDateTimeStartOfDay := date_time_start_of_day.
        Definition OpDateTimeStartOfWeek := date_time_start_of_week.
        Definition OpDateTimeStartOfMonth := date_time_start_of_month.
        Definition OpDateTimeStartOfQuarter := date_time_start_of_quarter.
        Definition OpDateTimeStartOfYear := date_time_start_of_year.
        Definition OpDateTimeEndOfDay := date_time_end_of_day.
        Definition OpDateTimeEndOfWeek := date_time_end_of_week.
        Definition OpDateTimeEndOfMonth := date_time_end_of_month.
        Definition OpDateTimeEndOfQuarter := date_time_end_of_quarter.
        Definition OpDateTimeEndOfYear := date_time_end_of_year.
        Definition OpDateTimeFormatFromString := date_time_format_from_string.
        Definition OpDateTimeFromString := date_time_from_string.
        Definition OpDateTimeMax := date_time_max.
        Definition OpDateTimeMin := date_time_min.
        Definition OpDateTimeDurationFromString := date_time_duration_from_string.
        Definition OpDateTimeDurationFromSeconds := date_time_duration_from_seconds.
        Definition OpDateTimeDurationFromMinutes := date_time_duration_from_minutes.
        Definition OpDateTimeDurationFromHours := date_time_duration_from_hours.
        Definition OpDateTimeDurationFromDays := date_time_duration_from_days.
        Definition OpDateTimeDurationFromWeeks := date_time_duration_from_weeks.
        Definition OpDateTimePeriodFromString := date_time_period_from_string.
        Definition OpDateTimePeriodFromDays := date_time_period_from_days.
        Definition OpDateTimePeriodFromWeeks := date_time_period_from_weeks.
        Definition OpDateTimePeriodFromMonths := date_time_period_from_months.
        Definition OpDateTimePeriodFromQuarters := date_time_period_from_quarters.
        Definition OpDateTimePeriodFromYears := date_time_period_from_years.

      End Unary.
      
      Module Binary.
        (* for ocaml *)
        Definition date_time_format
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_format).
        Definition date_time_add
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_add).
        Definition date_time_subtract
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_subtract).
        Definition date_time_add_period
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_add_period).
        Definition date_time_subtract_period
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_subtract_period).
        Definition date_time_is_same
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_same).
        Definition date_time_is_before
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_before).
        Definition date_time_is_after
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_after).
        Definition date_time_diff
          := OpForeignBinary (enhanced_binary_date_time_op (bop_date_time_diff)).
        
        (* for coq style syntax *)
        Definition OpDateTimeFormat := date_time_format.
        Definition OpDateTimeAdd := date_time_add.
        Definition OpDateTimeSubtract := date_time_subtract.
        Definition OpDateTimeIsBefore := date_time_is_before.
        Definition OpDateTimeIsAfter := date_time_is_after.
        Definition OpDateTimeDiff := date_time_diff.
        
      End Binary.
    End Ops.
  End Enhanced.
End CompEnhanced.  
