import Jellium

/-!
Fail if a local declaration depends on `sorryAx` or a nonstandard axiom.
The final equality's remaining hypotheses are explicitly named literature
interfaces. The axiom check does not prove the physical interpretation of those
interfaces. See LITERATURE.txt and the printed equality type below.
-/

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  let mut definitionCount : Nat := 0
  let mut failures : Array (Name × Array Name) := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `Jellium && !name.isInternalDetail then
      match info with
      | .thmInfo _ => theoremCount := theoremCount + 1
      | .defnInfo _ => definitionCount := definitionCount + 1
      | _ => pure ()
      let axioms ← liftCoreM (Lean.collectAxioms name)
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      if !unexpected.isEmpty then
        failures := failures.push (name, unexpected)
  if theoremCount == 0 then
    logError "Audit imported no Jellium theorems"
  else if failures.isEmpty then
    logInfo m!"Checked {theoremCount} theorem declarations and {definitionCount} definitions"
    logInfo "No sorryAx or additional axioms. This audit does not discharge theorem hypotheses."
  else
    logError m!"Unexpected axiom dependencies {failures}"

#print axioms Jellium.CoulombForm.core_fluid_identity
#print axioms Jellium.Localization.bounded_transition_layer_lower_bound
#print axioms Jellium.Upper.upper_le_of_trial_bounds
#print axioms Jellium.Upper.counting_error_of_cell_bounds
#print axioms Jellium.Upper.quantitative_error
#print axioms Jellium.UpperCoverage.average_coverage_exact
#print axioms Jellium.UniformCounting.selectedSum_uniform_bounds
#print axioms Jellium.UniformCounting.selectedSum_counting_error
#print axioms Jellium.UniformCounting.selectedSum_uniform_convergence
#print axioms Jellium.UpperPhysical.fixed_packing_uniform_rate
#print axioms Jellium.UpperPhysical.fixed_packing_uniform_upper
#print axioms Jellium.UpperDensity.Inputs.average_uniform_bounds
#print axioms Jellium.InnerDensity.discrepancy_l1
#print axioms Jellium.InnerDensity.discrepancy_coulomb_tendsto_zero
#print axioms Jellium.NeutralizationGeometry.exists_prepared_annulus
#print axioms Jellium.Neutralization.shell_cancellation_identity
#print axioms Jellium.Neutralization.shell_correction_bound
#print axioms Jellium.Neutralization.shell_correction_bound_at_outer_radius
#print axioms Jellium.Neutralization.potential_constant_inside
#print axioms Jellium.Neutralization.core_shell_interaction
#print axioms Jellium.Neutralization.select_orbitals
#print axioms Jellium.Neutralization.exists_neutral_completion_with_monopole
#print axioms Jellium.Neutralization.exists_neutral_completion
#print axioms Jellium.LowerPhysical.exists_sector_le
#print axioms Jellium.LowerPhysical.lower_comparison
#print axioms Jellium.PeriodicSelected.trial_double_bounds
#print axioms Jellium.UpperDensity.Inputs.localized_lower_bound
#print axioms Jellium.UpperPhysical.upper_comparison
#print axioms Jellium.Conjecture51.equality
#print axioms Jellium.Main.equality
#print axioms Jellium.Main.coupling_equality
#print axioms Jellium.EnergyScaling.parameter_scaling_of_density_scaling
#print axioms Jellium.EnergyScaling.equality_of_unit_parameter
#print axioms Jellium.EnergyScaling.equality_iff_coupling_equality

-- Check the actual proof dependency graph, in addition to logical axioms.
-- Mathlib declarations cannot depend on declarations in this local project.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let retired : List Name := [
    `Jellium.Canonical, `Jellium.CanonicalConstruction,
    `Jellium.Canonicalization, `Jellium.ProbabilityApproximation,
    `Jellium.Domains.lattice_LN_admissible,
    `Jellium.contracted_energy_tendsto, `Jellium.contraction_energy_error,
    `Jellium.LowerConstructionObligations, `Jellium.UpperConstructionObligations,
    `Jellium.equality_of_construction_obligations, `Jellium.fixed_packing_bound]
  let mut pending : List Name := [``Jellium.Main.coupling_equality]
  let mut visited : NameSet := {}
  let mut failures : Array Name := #[]
  let required : List Name := [
    ``Jellium.Main.equality,
    ``Jellium.Conjecture51.equality,
    ``Jellium.EnergyScaling.parameter_scaling_of_density_scaling,
    ``Jellium.EnergyScaling.equality_of_unit_parameter,
    ``Jellium.EnergyScaling.equality_iff_coupling_equality,
    ``Jellium.LowerPhysical.exists_trial_sequence,
    ``Jellium.LowerPhysical.exists_sector_le,
    ``Jellium.Neutralization.exists_neutral_completion_with_monopole,
    ``Jellium.Neutralization.select_orbitals,
    ``Jellium.Neutralization.shell_correction_bound_at_outer_radius,
    ``Jellium.Neutralization.potential_constant_inside,
    ``Jellium.UpperPhysical.fixed_family_comparison,
    ``Jellium.MeasurableTrial.given_product_jellium,
    ``Jellium.Boundary.bounded_layer_from_standard_localization,
    ``Jellium.Upper.quantitative_error,
    ``Jellium.Upper.upper_le_of_trial_bounds]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !visited.contains name then
      visited := visited.insert name
      if retired.any (fun retiredName => retiredName.isPrefixOf name) then
        failures := failures.push name
      if let some info := env.find? name then
        for dependency in info.getUsedConstantsAsSet.toList do
          if dependency.getRoot == `Jellium then
            pending := dependency :: pending
  if failures.isEmpty then
    logInfo "The equality proof does not depend on the retired sector-assignment or contraction arguments."
  else
    logError m!"Retired proof dependencies remain {failures}"
  let missing := required.filter fun name => !visited.contains name
  if missing.isEmpty then
    logInfo "The equality proof uses every required main, lower, shell, upper, localization and scaling step."
  else
    logError m!"Required proof steps are absent from the equality dependency graph {missing}"

-- Print the full relative theorem, not just its axiom list.
#check Jellium.Conjecture51.equality
#check Jellium.Main.equality
#check Jellium.Main.coupling_equality
#print Jellium.Main.UnitParameterInputs
#check Jellium.Neutralization.exists_neutral_completion_with_monopole
#print Jellium.LowerPhysical.StandardLaws
#print Jellium.UpperPhysical.StandardLaws
#print Jellium.UpperDensity.LocalizationLaws
#print Jellium.TrialState.StateAPI
#print Jellium.Neutralization.StandardLaws
#print Jellium.Neutralization.OrbitalSample
