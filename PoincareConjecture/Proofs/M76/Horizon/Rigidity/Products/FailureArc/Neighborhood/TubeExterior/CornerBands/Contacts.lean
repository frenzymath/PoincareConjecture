import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Panels



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def incident (i j : Bool × Bool) : Prop := j.2 = if j.1 then i.2 else i.1

instance (i j : Bool × Bool) : Decidable (incident i j) :=
  inferInstanceAs (Decidable (j.2 = if j.1 then i.2 else i.1))

noncomputable def seamPoint (r δ : ℝ) (i : Bool × Bool) (axis : Bool) : P2 :=
  arcMap r i (if axis then δ else -δ)

theorem footprint_inter_edgeFootprint {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (i j : Bool × Bool) :
    footprint r δ i ∩ edgeFootprint r δ j =
      if incident i j then {seamPoint r δ i j.1} else ∅ := by
  classical
  rcases i with ⟨a,b⟩
  rcases j with ⟨axis,s⟩
  cases a <;> cases b <;> cases axis <;> cases s <;> ext z
  all_goals simp only [footprint,edgeFootprint,incident,seamPoint,arcMap,sign,
    Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,one_mul,neg_one_mul,
    max_eq_right hδ.le,max_eq_left (neg_nonpos.mpr hδ.le),sub_zero,
    mem_inter_iff,mem_ofPred_eq,mem_prod,mem_Icc,mem_singleton_iff,
    mem_empty_iff_false,Prod.ext_iff]
  all_goals aesop (add safe (by linarith))

theorem band_inter_panel {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (i j : Bool × Bool) :
    band r δ i ∩ panel r δ j =
      if incident i j then {seamPoint r δ i j.1} ×ˢ Icc (0 : ℝ) 1 else ∅ := by
  classical
  have h := footprint_inter_edgeFootprint hδ hδr i j
  by_cases hij : incident i j
  · rw [if_pos hij] at h ⊢
    ext z
    have hz := Set.ext_iff.mp h z.1
    simp only [band,panel,mem_inter_iff,mem_prod,mem_singleton_iff] at hz ⊢
    tauto
  · rw [if_neg hij] at h ⊢
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact notMem_empty z.1 (h.subset ⟨hz.1.1,hz.2.1⟩)

theorem edgeFootprints_pairwise_disjoint {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    Pairwise (fun i j : Bool × Bool => Disjoint (edgeFootprint r δ i) (edgeFootprint r δ j)) := by
  rintro ⟨axis₀,s₀⟩ ⟨axis₁,s₁⟩ hij
  apply disjoint_left.mpr
  intro z hz hw
  cases axis₀ <;> cases s₀ <;> cases axis₁ <;> cases s₁
  all_goals simp only [edgeFootprint,sign,Bool.false_eq_true,if_false,if_true,
    one_mul,neg_one_mul,mem_prod,mem_singleton_iff,mem_Icc] at hz hw
  all_goals first | exact hij rfl | linarith [hz.1,hz.2,hw.1,hw.2]

theorem panels_pairwise_disjoint {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    Pairwise (fun i j : Bool × Bool => Disjoint (panel r δ i) (panel r δ j)) := by
  intro i j hij
  exact disjoint_left.mpr (fun z hi hj =>
    disjoint_left.mp (edgeFootprints_pairwise_disjoint hδ hδr hij) hi.1 hj.1)

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
