import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.SignedCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.MarkedRimCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimGroup
import Mathlib.Topology.Metrizable.Uniformity










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

private instance : Fact (0 < (4 * (128 : ℝ))) := ⟨by norm_num⟩



theorem sourcePhase_frontier_signed_data
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (he : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) =
      (sourceSlab phi u v ∩ frontier R) ∪
        (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hdis : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    let N := sourceSlab phi u v
    let S : Set (frontier N) := Subtype.val ⁻¹' sourceSurface phi theta
    let O : Set (frontier N) :=
      Subtype.val ⁻¹' ((N ∩ frontier R) ∪ sourceSurface phi theta')
    sourceSurface phi theta ⊆ frontier N ∧
      IsClosed S ∧ IsClosed O ∧ S ∪ O = univ ∧
      (∀ x : frontier N, x ∈ S ∩ O ↔ (x : X) ∈ sourceSurface phi theta ∩ frontier R) ∧
      IsCompact (S ∩ O) ∧ (S ∩ O).Nonempty ∧
      ∀ x : ↥(S ∩ O),
        ∃ T : OpenPartialHomeomorph (frontier N) (ℝ × ℝ), (x : frontier N) ∈ T.source ∧
          (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
          ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0 := by
  classical
  let : TopologicalSpace.MetrizableSpace
      ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let N := sourceSlab phi u v
  let S0 := sourceSurface phi theta
  let S1 := sourceSurface phi theta'
  have hSF : S0 ⊆ frontier N := fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx))
  have hSN : S0 ⊆ N := hSF.trans he.closed.frontier_subset
  let S : Set (frontier N) := Subtype.val ⁻¹' S0
  let O : Set (frontier N) := Subtype.val ⁻¹' ((N ∩ frontier R) ∪ S1)
  have hSc : IsClosed S := (sourceSurface_isCompact phi theta).isClosed.preimage continuous_subtype_val
  have hOc : IsClosed O :=
    ((he.closed.inter isClosed_frontier).union
      (sourceSurface_isCompact phi theta').isClosed).preimage continuous_subtype_val
  have hcover : S ∪ O = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := hfront.subset x.property
    change (x : X) ∈ S0 ∨ (x : X) ∈ (N ∩ frontier R) ∪ S1
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have hrim (x : frontier N) : x ∈ S ∩ O ↔ (x : X) ∈ S0 ∩ frontier R := by
    change ((x : X) ∈ S0 ∧ ((x : X) ∈ N ∩ frontier R ∨ (x : X) ∈ S1)) ↔ _
    constructor
    · rintro ⟨hx, hOld | hOther⟩
      · exact ⟨hx, hOld.2⟩
      · exact (disjoint_left.mp hdis hx hOther).elim
    · intro hx
      exact ⟨hx.1, Or.inl ⟨hSN hx.1, hx.2⟩⟩
  have hrimset : S ∩ O = (Subtype.val : frontier N → X) ⁻¹' (S0 ∩ frontier R) :=
    Set.ext hrim
  have hcompact : IsCompact (S ∩ O) := by
    rw [hrimset]
    apply Topology.IsInducing.subtypeVal.isCompact_preimage'
      ((sourceSurface_isCompact phi theta).inter_right isClosed_frontier)
    simpa only [Subtype.range_coe] using inter_subset_left.trans hSF
  let rimEquiv : ↥(S ∩ O) ≃ₜ ↥(S0 ∩ frontier R) :=
    { toFun := fun x => ⟨x.val.val, (hrim x.val).mp x.property⟩
      invFun := fun x => ⟨⟨x.val, hSF x.property.1⟩, (hrim _).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hne : (S ∩ O).Nonempty := by
    let b : Metric.closedBall (0 : Fin 1 → ℝ) 1 := ⟨fun _ => 1, by simp⟩
    let z : hamiltonOneAnnulusRim := ⟨(b, 0), by simp [hamiltonOneAnnulusRim, b]⟩
    let x := rimEquiv.symm ((sourceRimCoordinates phi theta F).symm z)
    exact ⟨x, x.property⟩
  have hlocal (x : ↥(S ∩ O)) :
      ∃ T : OpenPartialHomeomorph (frontier N) (ℝ × ℝ), (x : frontier N) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0 := by
    have hxrim := (hrim x.val).mp x.property
    obtain ⟨psi, lambda, w, z, G, hpw, hpz, hlz, hxG, hGN, hGO, hGS⟩ :=
      hcorner x.val.val hxrim
    let G' := G.restr S1ᶜ
    have hS1c : IsOpen S1ᶜ := (sourceSurface_isCompact phi theta').isClosed.isOpen_compl
    have hG's : G'.source = G.source ∩ S1ᶜ := G.restr_source' S1ᶜ hS1c
    have hxG' : x.val.val ∈ G'.source := by
      rw [hG's]
      exact ⟨hxG, fun hx1 => disjoint_left.mp hdis hxrim.1 hx1⟩
    have hN' (y : X) (hy : y ∈ G'.source) : y ∈ N ↔ 0 ≤ psi (G' y) :=
      hGN y ((hG's.subset hy).1)
    have hS' (y : X) (hy : y ∈ G'.source) :
        y ∈ S0 ↔ psi (G' y) = 0 ∧ lambda (G' y) ≤ 0 := hGS y ((hG's.subset hy).1)
    have hO' (y : X) (hy : y ∈ G'.source) :
        y ∈ (N ∩ frontier R) ∪ S1 ↔ psi (G' y) = 0 ∧ 0 ≤ lambda (G' y) := by
      have hy1 : y ∉ S1 := (hG's.subset hy).2
      rw [mem_union, or_iff_left hy1]
      exact hGO y ((hG's.subset hy).1)
    obtain ⟨T, hxT, hTS, hTO, _⟩ := exists_intrinsic_signed_rim_chart
      G' psi lambda w z hpw hpz hlz hN' hS' hO' x.val hxG'
    exact ⟨T, hxT, hTS, hTO⟩
  exact ⟨hSF, hSc, hOc, hcover, hrim, hcompact, hne, hlocal⟩



theorem sourcePhase_frontier_pi1_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (he : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) =
      (sourceSlab phi u v ∩ frontier R) ∪
        (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hdis : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ hSF : sourceSurface phi theta ⊆ frontier (sourceSlab phi u v),
      ∀ x : sourceSurface phi theta,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSF) x) := by
  classical
  let : TopologicalSpace.MetrizableSpace
      ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let N := sourceSlab phi u v
  let S0 := sourceSurface phi theta
  let S1 := sourceSurface phi theta'
  let S : Set (frontier N) := Subtype.val ⁻¹' S0
  let O : Set (frontier N) := Subtype.val ⁻¹' ((N ∩ frontier R) ∪ S1)
  obtain ⟨hSF, hSc, hOc, hcover, hrim, hcompact, hne, hlocal⟩ :=
    sourcePhase_frontier_signed_data e phi F he hfront hdis hcorner
  let rimEquiv : ↥(S ∩ O) ≃ₜ ↥(S0 ∩ frontier R) :=
    { toFun := fun x => ⟨x.val.val, (hrim x.val).mp x.property⟩
      invFun := fun x => ⟨⟨x.val, hSF x.property.1⟩, (hrim _).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hpi (x : ↥(S ∩ O)) : Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (S ∩ O)) x) := by
    let r : C(↥(S ∩ O), ↥(S0 ∩ frontier R)) := ⟨rimEquiv, rimEquiv.continuous⟩
    have hr : Function.Injective (FundamentalGroup.map r x) :=
      FundamentalGroup.map_injective_of_leftInverse r
        ⟨rimEquiv.symm, rimEquiv.symm.continuous⟩ rimEquiv.symm_apply_apply x
    intro a b hab
    apply hr
    apply sourceRim_ambient_pi1_injective phi theta F (rimEquiv x)
    let j : C(frontier N, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let jR : C(↥(S0 ∩ frontier R), X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hc := FundamentalGroup.map_comp_apply r jR x
    have h := congrArg (FundamentalGroup.map j (VanKampen.inclusion (S ∩ O) x)) hab
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
    exact (hc a).symm.trans (h.trans (hc b))
  have hSpi := sides_pi1_injective_of_signed_rim_charts hSc hOc hcover hcompact hne hlocal hpi
    S (Or.inl rfl)
  let E : S0 ≃ₜ S :=
    { toFun := fun x => ⟨⟨x.val, hSF x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨hSF, ?_⟩
  intro x
  let Emap : C(S0, S) := ⟨E, E.continuous⟩
  have hEpi : Function.Injective (FundamentalGroup.map Emap x) :=
    FundamentalGroup.map_injective_of_leftInverse Emap
      ⟨E.symm, E.symm.continuous⟩ E.symm_apply_apply x
  intro a b hab
  apply hEpi
  apply hSpi (E x)
  have hc := FundamentalGroup.map_comp_apply Emap (VanKampen.inclusion S) x
  exact (hc a).symm.trans (hab.trans (hc b))

end PoincareConjecture.M76.HamiltonIntervalTorus
