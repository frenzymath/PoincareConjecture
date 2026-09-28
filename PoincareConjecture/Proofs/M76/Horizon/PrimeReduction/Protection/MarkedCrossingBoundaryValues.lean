import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalExteriorCompressionDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalExteriorBoundaryDetector









set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0:V2) 1
local notation "Q2" => sphere (0:V2) 1

theorem HamiltonMarkedProtectedBall.old_boundary_outside_open_patch_mem_exterior
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ→ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α→OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι+Fintype.card κ=3) (hi : Fintype.card ι=1)
    {x : LatticeHandleAmbient ι κ L} (hx : x∈frontier (latticeHandleDomain ι κ L))
    (hno : x.2 ∉ (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup) ''
      Metric.ball (0:κ→ℝ) (3/2)) : x∈closure (latticeHandleDomain ι κ L \ D) := by
  by_cases hxD : x∈D
  · have hmark : D∩frontier (latticeHandleDomain ι κ L)=hamiltonAttachingBlock ι κ L (3/2) := by
      rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
      · omega
      · exact hm
    obtain ⟨z,hz,hzx⟩ := hmark.subset ⟨hxD,hx⟩
    have hn : ‖z.2‖=(3/2:ℝ) := by
      apply le_antisymm (mem_closedBall_zero_iff.mp hz.2)
      apply le_of_not_gt
      intro hh
      exact hno ⟨z.2,mem_ball_zero_iff.mpr hh,congrArg Prod.snd hzx⟩
    have hxfront : x∈frontier D :=
      ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset ⟨hxD,hx⟩).1
    have hxT : x∈frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
      hamiltonMarkedProjection ι κ L ''
        (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2))) :=
      ⟨hxfront,fun hh => hh.2 ⟨z,⟨hz.1,mem_sphere_zero_iff_norm.mpr hn⟩,hzx⟩⟩
    exact ((b.closed_complement_lateral_contact he hdim hi).symm.subset hxT).1
  · exact subset_closure ⟨he.closed.frontier_subset hx,hxD⟩

private theorem crossing_parameters {d:ℝ} (hd:3<d) :
    let c:=(d-3)/(d-2)
    0<c ∧ c<1 ∧
      (∀t:ℝ, (d⁻¹+(1-2*d⁻¹)*((t+1)/2)) = (1+(1-2/d)*t)/2) ∧
      (∀t:ℝ, -c≤t ∧ t≤c →
        (3/2)/d ≤ d⁻¹+(1-2*d⁻¹)*((t+1)/2) ∧
        d⁻¹+(1-2*d⁻¹)*((t+1)/2) ≤ 1-(3/2)/d) := by
  dsimp only
  have hd0 : 0<d := by linarith
  have hd2 : 0<d-2 := by linarith
  refine ⟨div_pos (by linarith) hd2,(div_lt_one hd2).mpr (by linarith),?_,?_⟩
  · intro t
    rw [div_eq_mul_inv]
    ring
  · intro t ht
    have hc : ((d-3)/(d-2))*(d-2)=d-3 := div_mul_cancel₀ _ (ne_of_gt hd2)
    have hm := mul_le_mul_of_nonneg_right ht.1 hd2.le
    have hp := mul_le_mul_of_nonneg_right ht.2 hd2.le
    have hmul : (d⁻¹+(1-2*d⁻¹)*((t+1)/2))*d = (d+(d-2)*t)/2 := by
      field_simp
      ring
    constructor
    · apply (div_le_iff₀ hd0).mpr
      rw [hmul]
      nlinarith
    · have hh : (d⁻¹+(1-2*d⁻¹)*((t+1)/2))*d ≤ d-3/2 := by
        rw [hmul]
        nlinarith
      have hc2 : ((3/2:ℝ)/d)*d=3/2 := div_mul_cancel₀ _ (ne_of_gt hd0)
      nlinarith

private theorem exists_small_segment_representative
    {κ : Type*} [Fintype κ] (L:Submodule ℤ (κ→ℝ))
    {v:κ→ℝ} (hv:v∈L) {t r:ℝ} (ht:0≤t ∧ t≤1)
    (hsmall:t*‖v‖≤r ∨ (1-t)*‖v‖≤r) :
    ∃ z:κ→ℝ, z∈closedBall (0:κ→ℝ) r ∧
      (QuotientAddGroup.mk z : (κ→ℝ)⧸L.toAddSubgroup)=QuotientAddGroup.mk (t • v) := by
  rcases hsmall with h | h
  · refine ⟨t • v,?_,rfl⟩
    simpa [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] using h
  · refine ⟨(t-1) • v,?_,?_⟩
    · rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      nlinarith
    · apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hh : (t-1) • v-t • v= -v := by module
      rw [hh]
      exact L.neg_mem hv

theorem HamiltonMarkedProtectedBall.exists_original_detected_exterior_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ→ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α→OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι+Fintype.card κ=3) (hi : Fintype.card ι=1) :
    let E:=closure (latticeHandleDomain ι κ L \ D)
    ∃ (v:κ→ℝ) (f:C(D2,E)) (gamma:C(Q2,frontier E))
      (F:C(frontier E,(κ→ℝ)⧸L.toAddSubgroup)),
      v∈L ∧ v≠0 ∧ 3<‖v‖ ∧
      (∀ x:Q2, (f ⟨x,sphere_subset_closedBall x.property⟩ : LatticeHandleAmbient ι κ L)=gamma x) ∧
      (∀ x:Q2, x.val 0= -1 → |x.val 1|≤(‖v‖-3)/(‖v‖-2) →
        F (gamma x)=QuotientAddGroup.mk
          ((‖v‖⁻¹+(1-2*‖v‖⁻¹)*((x.val 1+1)/2)) • v)) ∧
      ∀ x:Q2, ¬(x.val 0= -1 ∧ |x.val 1|<(‖v‖-3)/(‖v‖-2)) →
        F (gamma x) ∈ (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup) ''
          closedBall (0:κ→ℝ) (3/2) := by
  classical
  dsimp only
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let X:=LatticeHandleAmbient ι κ L
  let R:=latticeHandleDomain ι κ L
  let E:=closure (R \ D)
  obtain ⟨v,f,hv,hv0,hlen,hmin,hfix,hout,hin,hrim⟩ :=
    b.exists_original_exterior_continuous_disk he hdim hi
  obtain ⟨F,hFminus,hFdisk⟩ := b.exists_original_exterior_boundary_detector he hdim hi
  let gamma:C(Q2,frontier E):=
    ⟨fun x=>⟨f ⟨x,sphere_subset_closedBall x.property⟩,hrim x⟩,by fun_prop⟩
  let theta:V2→ℝ:=fun x=>‖v‖⁻¹+(1-2*‖v‖⁻¹)*((x 1+1)/2)
  have hn:0<‖v‖:=norm_pos_iff.mpr hv0
  obtain ⟨hc0,hc1,hthetaformula,hcentral⟩ := crossing_parameters hlen
  have hinv:0<‖v‖⁻¹ ∧ ‖v‖⁻¹<1/2 :=
    ⟨inv_pos.mpr hn,(inv_lt_comm₀ hn (by norm_num)).mpr (by norm_num; linarith)⟩
  have hcoord (x:D2) (i:Fin 2) : |x.val i|≤1 :=
    (Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm _ i).trans
      (mem_closedBall_zero_iff.mp x.property)
  have htrange (x:D2) : 0≤theta x ∧ theta x≤1 := by
    have hh:=abs_le.mp (hcoord x 1)
    dsimp [theta]
    constructor <;> nlinarith [hinv.1,hinv.2]
  have hmark : D∩frontier R=hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hnegativeD (x:D2) (hs:|x.val 0|=1)
      (ht:theta x*‖v‖≤3/2 ∨ (1-theta x)*‖v‖≤3/2) :
      markedCrossingSquare (ι:=ι) L v x∈D := by
    obtain ⟨z,hz,hzq⟩ := exists_small_segment_representative L hv (htrange x) ht
    apply (hmark.symm.subset ?_).1
    refine ⟨((fun _:ι=>x.val 0),z),⟨?_,hz⟩,?_⟩
    · rw [mem_sphere_zero_iff_norm,pi_norm_const,Real.norm_eq_abs]
      exact hs
    · change ((fun _:ι=>x.val 0),(QuotientAddGroup.mk z : (κ→ℝ)⧸L.toAddSubgroup)) =
        ((fun _:ι=>x.val 0),QuotientAddGroup.mk (theta x • v))
      exact congrArg (Prod.mk (fun _:ι=>x.val 0)) hzq
  have hverticalD (x:D2) (ht:|x.val 1|=1) : markedCrossingSquare (ι:=ι) L v x∈D := by
    have hsmall : theta x*‖v‖≤1 ∨ (1-theta x)*‖v‖≤1 := by
      rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp ht with ht | ht
      · right
        have hth:theta x=1-‖v‖⁻¹:=by dsimp [theta]; rw [ht]; ring
        rw [hth]
        simpa using (le_of_eq (inv_mul_cancel₀ (ne_of_gt hn)))
      · left
        have hth:theta x=‖v‖⁻¹:=by dsimp [theta]; rw [ht]; ring
        rw [hth,inv_mul_cancel₀ (ne_of_gt hn)]
    obtain ⟨z,hz,hzq⟩ := exists_small_segment_representative L hv (htrange x) hsmall
    have hKD : hamiltonHandleBlock ι κ L 1⊆D := by
      rcases b.position with ⟨hz,_⟩ | ⟨_,hcore,_⟩
      · omega
      · exact hcore
    apply hKD
    refine ⟨((fun _:ι=>x.val 0),z),⟨?_,hz⟩,?_⟩
    · rw [mem_closedBall_zero_iff,pi_norm_const,Real.norm_eq_abs]
      exact hcoord x 0
    · exact congrArg (Prod.mk (fun _:ι=>x.val 0)) hzq
  refine ⟨v,f,gamma,F,hv,hv0,hlen,(fun _=>rfl),?_,?_⟩
  · intro x hs ht
    let y:D2:=⟨x,sphere_subset_closedBall x.property⟩
    have ht' := hcentral (x.val 1) (abs_le.mp ht)
    have hno : (markedCrossingSquare (ι:=ι) L v y).2 ∉
        (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup) ''
          Metric.ball (0:κ→ℝ) (3/2) := by
      rintro ⟨z,hz,hzq⟩
      have hw:theta y • v-z∈L:=QuotientAddGroup.eq_iff_sub_mem.mp hzq.symm
      have hh:=shortest_lattice_segment_avoids_translates L hv hv0 hmin
        (r:=3/2) (by norm_num) (by linarith) ht' _ hw
      change (3/2:ℝ)≤‖theta y • v-(theta y • v-z)‖ at hh
      simp only [sub_sub_cancel] at hh
      exact (not_lt_of_ge hh) (mem_ball_zero_iff.mp hz)
    have hqfront:markedCrossingSquare (ι:=ι) L v y∈frontier R := by
      change _∈frontier (closedBall (0:ι→ℝ) 1 ×ˢ univ)
      rw [frontier_prod_univ_eq,frontier_closedBall _ (by norm_num : (1:ℝ)≠0)]
      refine ⟨?_,mem_univ _⟩
      rw [mem_sphere_zero_iff_norm]
      change ‖fun _:ι=>x.val 0‖=1
      rw [hs,pi_norm_const,Real.norm_eq_abs]
      norm_num
    have hqE:=b.old_boundary_outside_open_patch_mem_exterior he hdim hi hqfront hno
    have hfv:=hfix y hqE
    have hlow : (gamma x).val.1=(fun _:ι=>-1) := by
      change (f y).val.1=_
      rw [hfv]
      change (fun _:ι=>x.val 0)=(fun _:ι=>-1)
      rw [hs]
    exact (hFminus (gamma x) hlow).trans (congrArg Prod.snd hfv)
  · intro x hx
    let y:D2:=⟨x,sphere_subset_closedBall x.property⟩
    by_cases hyD:markedCrossingSquare (ι:=ι) L v y∈D
    · exact hFdisk (gamma x) (Or.inl (hin y hyD).1)
    have hfv:=hout y hyD
    have htne:|x.val 1|≠1:=fun hh=>hyD (hverticalD y hh)
    have hsabs:|x.val 0|=1 := by
      by_contra hh
      have hsmall:‖x.val‖<1 := (pi_norm_lt_iff (by norm_num)).mpr (by
        intro i
        fin_cases i
        · exact (Real.norm_eq_abs _).symm ▸ lt_of_le_of_ne (hcoord y 0) hh
        · exact (Real.norm_eq_abs _).symm ▸ lt_of_le_of_ne (hcoord y 1) htne)
      rw [mem_sphere_zero_iff_norm.mp x.property] at hsmall
      exact lt_irrefl _ hsmall
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hsabs with hs | hs
    · apply hFdisk (gamma x) (Or.inr ?_)
      change (f y).val.1=_
      rw [hfv]
      change (fun _:ι=>x.val 0)=(fun _:ι=>1)
      rw [hs]
    · exfalso
      apply hyD
      apply hnegativeD y hsabs
      have htc : (‖v‖-3)/(‖v‖-2) ≤ |x.val 1| := le_of_not_gt (fun h=>hx ⟨hs,h⟩)
      have hc : ((‖v‖-3)/(‖v‖-2))*(‖v‖-2)=‖v‖-3 :=
        div_mul_cancel₀ _ (by linarith)
      have hmul : theta y*‖v‖=(‖v‖+(‖v‖-2)*x.val 1)/2 := by
        dsimp [theta,y]
        field_simp
        ring
      rcases le_abs.mp htc with ht | ht
      · right
        have hh:=mul_le_mul_of_nonneg_right ht (show 0≤‖v‖-2 by linarith)
        nlinarith
      · left
        have hh:=mul_le_mul_of_nonneg_right ht (show 0≤‖v‖-2 by linarith)
        nlinarith

end PoincareConjecture.M76
