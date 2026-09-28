import PoincareConjecture.Statements.M67

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M68ProfileInput
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (HX : M67Conclusion X) where
  T₁ : ℝ
  T₂ : ℝ
  ordered : 0 ≤ T₁ ∧ T₁ ≤ T₂ ∧ T₂ ≤ T
  chronology : M67FiniteChronology
    (↑P.surgery_times : Set ℝ) T₁ T₂

def M68ProfileInput.start
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) : Set.Icc (0 : ℝ) T :=
  ⟨I.T₁, I.ordered.1, I.ordered.2.1.trans I.ordered.2.2⟩

def M68ProfileInput.time
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX)
    (t : Set.Icc I.T₁ I.T₂) : Set.Icc (0 : ℝ) T :=
  ⟨t.1, I.ordered.1.trans t.2.1, t.2.2.trans I.ordered.2.2⟩

noncomputable def m68Profile
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) (t : ℝ) : ℝ :=
  let w₁ := X.width I.start
  let a₁ := 1 + 4 * I.T₁
  let a := 1 + 4 * t
  w₁ * Real.rpow (a / a₁) ((3 : ℝ) / 4) +
    2 * Real.pi * Real.rpow a₁ ((1 : ℝ) / 4) * Real.rpow a ((3 : ℝ) / 4) -
    2 * Real.pi * a

structure M68ProfileConclusion
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {HX : M67Conclusion X}
    (I : M68ProfileInput X HX) where
  clock_positive : ∀ t : Set.Icc I.T₁ I.T₂, 0 < 1 + 4 * t.1
  profile_initial : m68Profile I I.T₁ = X.width I.start
  profile_equation : ∀ t : Set.Icc I.T₁ I.T₂,
    HasDerivAt (m68Profile I) (-2 * Real.pi +
      3 * m68Profile I t.1 / (1 + 4 * t.1)) t.1
  width_bound : ∀ t : Set.Icc I.T₁ I.T₂,
    X.width (M68ProfileInput.time I t) ≤ m68Profile I t.1

end PoincareConjecture
