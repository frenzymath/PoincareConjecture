import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.StandardPL
import PoincareConjecture.Proofs.M76.Rigidity.MeridianParameter
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "W" => (V2 × ℝ)
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L


noncomputable def diskCircleParameter (z : W) : D × C := by
  classical
  exact (if hz : z.1 ∈ D then ⟨z.1, hz⟩ else ⟨0, mem_closedBall_self zero_le_one⟩, (z.2 : C))

theorem diskCircleParameter_apply (z : V2) (hz : z ∈ D) (t : ℝ) :
    diskCircleParameter (z, t) = (⟨z, hz⟩, (t : C)) := by
  simp [diskCircleParameter, hz]

theorem continuousOn_diskCircleParameter : ContinuousOn diskCircleParameter (D ×ˢ univ) := by
  have hf : ContinuousOn (fun z : W => (diskCircleParameter z).1) (D ×ˢ univ) :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (continuous_fst.continuousOn.congr (fun z hz => by
        simp only [Function.comp_apply, diskCircleParameter, dif_pos hz.1]))
  exact hf.prodMk ((AddCircle.continuous_mk' p).comp_continuousOn continuous_snd.continuousOn)

theorem diskCircleParameter_period (z : W) :
    diskCircleParameter (z.1, z.2 + p) = diskCircleParameter z := by
  simp [diskCircleParameter]


theorem polyhedralPL_standardMeridianBoxParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (a b : ℝ)
    {l u : ℝ} (hlu : l < u) :
    PolyhedralPLInCharts d (standardMeridianBandParameter a b) (D ×ˢ Icc l u) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBox hlu
  have hv : FinitePiecewiseAffineOn (standardMeridianBandAffineLift a b) (D ×ˢ Icc l u) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine (standardMeridianBandAffineLift a b)⟩
  exact (hd.polyhedralPL_projection hv).congr
    (fun z _ => standardMeridianBandAffineLift_projection a b z)

theorem injOn_standardMeridianBoxParameter (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) {l u : ℝ} (hwidth : u < l + p) :
    InjOn (standardMeridianBandParameter a b) (D ×ˢ Icc l u) := by
  intro z hz w hw heq
  have hparam (v : W) (hv : v.1 ∈ D) : standardMeridianBandParameter a b v =
      (standardSlabMeridianCoordinates a b hab hshort (⟨v.1, hv⟩, (v.2 : C)) : X) :=
    (standardSlabMeridianCoordinates_coe a b hab hshort ⟨v.1, hv⟩ v.2).symm
  rw [hparam z hz.1, hparam w hw.1] at heq
  have hh := (standardSlabMeridianCoordinates a b hab hshort).injective (Subtype.ext heq)
  have hfirst := congrArg (fun x : D × C => (x.1 : V2)) hh
  have htime := congrArg Prod.snd hh
  exact Prod.ext hfirst ((AddCircle.coe_eq_coe_iff_of_mem_Ico
    ⟨hz.2.1, hz.2.2.trans_lt hwidth⟩ ⟨hw.2.1, hw.2.2.trans_lt hwidth⟩).mp htime)



theorem polyhedralPL_diskCircle_signed_parameter
    {Y α : Type*} [TopologicalSpace Y] {e : α → OpenPartialHomeomorph Y V3}
    {N : Set Y} (he : PLDomain e N) (G : C(D × C, Y))
    (hperiod : PolyhedralPLInCharts e (G ∘ diskCircleParameter) (D ×ˢ Icc 0 p)) :
    PolyhedralPLInCharts e (G ∘ diskCircleParameter) (D ×ˢ Icc (-1 : ℝ) 1) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBox (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨J0, hJ0, hJ0S⟩ := exists_finite_hamiltonMeridianBox (by norm_num : (-1 : ℝ) < 0)
  obtain ⟨J1, hJ1, hJ1S⟩ := exists_finite_hamiltonMeridianBox (by norm_num : (0 : ℝ) < 1)
  let f := G ∘ diskCircleParameter
  have hplus : PolyhedralPLInCharts e f J1.space := hperiod.restrict_finite J1 hJ1 (by
    intro z hz
    obtain ⟨hzD, hz0, hz1⟩ := hJ1S.subset hz
    exact ⟨hzD, hz0, by linarith⟩)
  let A : W →ᴬ[ℝ] W :=
    (ContinuousAffineEquiv.constVAdd ℝ W (0, p)).toContinuousAffineMap
  have hAval (z : W) : A z = (z.1, z.2 + p) := by
    change ((0 : V2) + z.1, p + z.2) = _
    rw [zero_add, add_comm p z.2]
  have hA : FinitePiecewiseAffineOn A J0.space := ⟨J0, hJ0, rfl, J0.affineOnFaces_affine A⟩
  have hmap : MapsTo A J0.space (D ×ˢ Icc 0 p) := by
    intro z hz
    rw [hAval]
    obtain ⟨hzD, hzm, hz0⟩ := hJ0S.subset hz
    exact ⟨hzD, by linarith, by linarith⟩
  have hminus : PolyhedralPLInCharts e f J0.space :=
    (hperiod.comp_finitePiecewiseAffineOn J0 hJ0 hA hmap).congr (by
      intro z _
      change G (diskCircleParameter (A z)) = G (diskCircleParameter z)
      rw [hAval, diskCircleParameter_period])
  let J : Bool → SimplicialComplex ℝ W := fun i => cond i J1 J0
  have hJ (i : Bool) : (J i).faces.Finite := by cases i <;> assumption
  have hPL (i : Bool) : PolyhedralPLInCharts e f (J i).space := by cases i <;> assumption
  have hc : ContinuousOn f K.space := G.continuous.comp_continuousOn
    (continuousOn_diskCircleParameter.mono (fun z hz => ⟨(hKS.subset hz).1, mem_univ _⟩))
  have hcover : K.space ⊆ ⋃ i, (J i).space := by
    intro z hz
    obtain ⟨hzD, hzm, hz1⟩ := hKS.subset hz
    by_cases ht : 0 ≤ z.2
    · exact mem_iUnion.mpr ⟨true, hJ1S.symm.subset ⟨hzD, ht, hz1⟩⟩
    · exact mem_iUnion.mpr ⟨false, hJ0S.symm.subset ⟨hzD, hzm, (not_le.mp ht).le⟩⟩
  exact hKS ▸ polyhedralPLInCharts_of_finite_cover he.cover he.compatible K hK J hJ hc hPL hcover

end PoincareConjecture.M76.HamiltonIntervalTorus
