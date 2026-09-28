import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalCoreLateralRetraction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedLatticeCrossingArc

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0:V2) 1
local notation "Q2" => sphere (0:V2) 1

noncomputable def markedCrossingSquare {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ→ℝ)) (v : κ→ℝ) (x : V2) : LatticeHandleAmbient ι κ L :=
  hamiltonMarkedProjection ι κ L
    ((fun _ => x 0), (‖v‖⁻¹ + (1-2*‖v‖⁻¹)*((x 1+1)/2)) • v)

theorem HamiltonMarkedProtectedBall.exists_original_exterior_continuous_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ (v : κ→ℝ) (f : C(D2,E)), v∈L ∧ v≠0 ∧ 3<‖v‖ ∧
      (∀ w : κ→ℝ, w∈L → w≠0 → ‖v‖≤‖w‖) ∧
      (∀ x:D2, markedCrossingSquare (ι:=ι) L v x ∈ E →
        (f x:LatticeHandleAmbient ι κ L) = markedCrossingSquare L v x) ∧
      (∀ x:D2, markedCrossingSquare (ι:=ι) L v x ∉ D →
        (f x:LatticeHandleAmbient ι κ L) = markedCrossingSquare L v x) ∧
      (∀ x:D2, markedCrossingSquare (ι:=ι) L v x ∈ D →
        (f x:LatticeHandleAmbient ι κ L) ∈ D ∩ frontier E) ∧
      ∀ x:Q2, (f ⟨x,sphere_subset_closedBall x.property⟩:
        LatticeHandleAmbient ι κ L) ∈ frontier E := by
  classical
  dsimp only
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  let O := hamiltonMarkedProjection ι κ L ''
    (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
  let T := frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
    hamiltonMarkedProjection ι κ L ''
      (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2)))
  obtain ⟨v,hv,hv0,hvlen,hmin,_,_⟩ :=
    b.exists_marked_lattice_crossing_segment hdim hi
  obtain ⟨hEE0,r,hfix,hlat⟩ := b.exists_original_exterior_retraction_with_lateral he hdim hi
  obtain ⟨hEc,hER,_,hcontact,_,_,hfront⟩ := b.closed_complement_geometry he hdim hi
  have hTD : T ⊆ D := fun _ hx => (hcontact.symm.subset hx).2
  have hTF : T ⊆ frontier E := fun _ hx => hfront.symm.subset (Or.inl hx)
  have hvnorm : 0<‖v‖ := norm_pos_iff.mpr hv0
  have hangle : 0 < ‖v‖⁻¹ ∧ ‖v‖⁻¹ < (1/2:ℝ) := by
    exact ⟨inv_pos.mpr hvnorm,(inv_lt_comm₀ hvnorm (by norm_num)).mpr (by norm_num; linarith)⟩
  have hxcoord (x:D2) (i:Fin 2) : |x.val i|≤1 := by
    exact (Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm _ i).trans
      (mem_closedBall_zero_iff.mp x.property)
  let theta : V2→ℝ := fun x => ‖v‖⁻¹ + (1-2*‖v‖⁻¹)*((x 1+1)/2)
  have htheta (x:D2) : theta x ∈ Icc (1/‖v‖) (1-1/‖v‖) := by
    have hh := abs_le.mp (hxcoord x 1)
    dsimp [theta]
    simp only [one_div]
    constructor <;> nlinarith [hangle.1,hangle.2]
  have hqR (x:D2) : markedCrossingSquare (ι:=ι) L v x ∈ R := by
    refine ⟨?_,mem_univ _⟩
    change (fun _:ι => x.val 0) ∈ closedBall (0:ι→ℝ) 1
    rw [mem_closedBall_zero_iff,pi_norm_const,Real.norm_eq_abs]
    exact hxcoord x 0
  have hqO (x:D2) : markedCrossingSquare (ι:=ι) L v x ∉ O := by
    rintro ⟨z,hz,hzx⟩
    have hq := congrArg Prod.snd hzx
    have hw : theta x • v-z.2 ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp hq.symm
    have hh := shortest_lattice_segment_avoids_translates L hv hv0 hmin
      (r:=1) (by norm_num) (by linarith) (htheta x) _ hw
    simp only [sub_sub_cancel] at hh
    exact (not_lt_of_ge hh) (mem_ball_zero_iff.mp hz.2)
  let q : C(D2,↥(R \ O)) :=
    ⟨fun x => ⟨markedCrossingSquare L v x,⟨hqR x,hqO x⟩⟩,by
      apply Continuous.subtype_mk
      change Continuous (fun x:D2 => ((fun _:ι => x.val 0),
        (QuotientAddGroup.mk (theta x • v) : (κ→ℝ) ⧸ L.toAddSubgroup)))
      apply Continuous.prodMk
      · exact continuous_pi (fun _ => (continuous_apply 0).comp continuous_subtype_val)
      · apply continuous_quotient_mk'.comp
        dsimp [theta]
        have hc : Continuous (fun x:D2 => x.val 1) :=
          (continuous_apply 1).comp continuous_subtype_val
        exact (continuous_const.add (continuous_const.mul
          ((hc.add_const 1).div_const 2))).smul continuous_const⟩
  let f : C(D2,E) := r.comp q
  have hfout (x:D2) (hx:markedCrossingSquare (ι:=ι) L v x ∉ D) :
      (f x:X) = markedCrossingSquare L v x :=
    hfix (q x) (subset_closure ⟨hqR x,hx⟩)
  have hfin (x:D2) (hx:markedCrossingSquare (ι:=ι) L v x ∈ D) :
      (f x:X) ∈ D ∩ frontier E :=
    ⟨hTD (hlat (q x) hx),hTF (hlat (q x) hx)⟩
  refine ⟨v,f,hv,hv0,hvlen,hmin,(fun x hx => hfix (q x) hx),hfout,hfin,?_⟩
  intro x
  let y:D2 := ⟨x,sphere_subset_closedBall x.property⟩
  by_cases hyD : markedCrossingSquare (ι:=ι) L v y ∈ D
  · exact (hfin y hyD).2
  rw [hfout y hyD]
  have hfaces : |x.val 0|=1 ∨ |x.val 1|=1 := by
    by_contra hn
    push Not at hn
    have hsmall : ‖x.val‖<1 := (pi_norm_lt_iff (by norm_num)).mpr (by
      intro i
      fin_cases i
      · exact (Real.norm_eq_abs _).symm ▸ lt_of_le_of_ne (hxcoord y 0) hn.1
      · exact (Real.norm_eq_abs _).symm ▸ lt_of_le_of_ne (hxcoord y 1) hn.2)
    rw [mem_sphere_zero_iff_norm.mp x.property] at hsmall
    exact (lt_irrefl _ hsmall)
  rcases hfaces with hs | ht
  · apply hfront.symm.subset
    refine Or.inr ⟨subset_closure ⟨hqR y,hyD⟩,?_⟩
    change markedCrossingSquare L v y ∈ frontier (closedBall (0:ι→ℝ) 1 ×ˢ univ)
    rw [frontier_prod_univ_eq,frontier_closedBall _ (by norm_num : (1:ℝ)≠0)]
    refine ⟨?_,mem_univ _⟩
    rw [mem_sphere_zero_iff_norm]
    change ‖fun _:ι => x.val 0‖=1
    rwa [pi_norm_const,Real.norm_eq_abs]
  · exfalso
    apply hyD
    have hKD : hamiltonHandleBlock ι κ L 1 ⊆ D := by
      rcases b.position with ⟨hz,_⟩ | ⟨_,hcore,_⟩
      · omega
      · exact hcore
    have hunit : ‖v‖⁻¹ • v ∈ closedBall (0:κ→ℝ) 1 := by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvnorm),inv_mul_cancel₀ (ne_of_gt hvnorm)]
    have hnegunit : -(‖v‖⁻¹ • v) ∈ closedBall (0:κ→ℝ) 1 := by
      simpa only [mem_closedBall_zero_iff,norm_neg] using hunit
    have hy0 : (fun _:ι => y.val 0)∈closedBall (0:ι→ℝ) 1 := (hqR y).1
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp ht with ht | ht
    · refine hKD ⟨((fun _:ι => y.val 0),-(‖v‖⁻¹ • v)),⟨hy0,hnegunit⟩,?_⟩
      change ((fun _:ι=>y.val 0), (QuotientAddGroup.mk (-(‖v‖⁻¹ • v)) :
        (κ→ℝ) ⧸ L.toAddSubgroup)) = ((fun _:ι=>y.val 0),QuotientAddGroup.mk (theta y • v))
      apply congrArg (fun z : (κ→ℝ) ⧸ L.toAddSubgroup => ((fun _:ι=>y.val 0),z))
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change -(‖v‖⁻¹ • v)-theta y • v ∈ L.toAddSubgroup
      have hth : theta y=1-‖v‖⁻¹ := by dsimp [theta,y]; rw [ht]; ring
      rw [hth]
      have hh : -(‖v‖⁻¹ • v)-(1-‖v‖⁻¹) • v = -v := by module
      rw [hh]
      exact L.neg_mem hv
    · refine hKD ⟨((fun _:ι => y.val 0),‖v‖⁻¹ • v),⟨hy0,hunit⟩,?_⟩
      have hth : theta y=‖v‖⁻¹ := by dsimp [theta,y]; rw [ht]; ring
      change hamiltonMarkedProjection ι κ L _ = hamiltonMarkedProjection ι κ L _
      change hamiltonMarkedProjection ι κ L ((fun _=>y.val 0),‖v‖⁻¹ • v) =
        hamiltonMarkedProjection ι κ L ((fun _=>y.val 0),theta y • v)
      rw [hth]

end PoincareConjecture.M76
