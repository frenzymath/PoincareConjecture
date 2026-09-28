import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCrossingBoundaryValues
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachingDiskTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.QuotientLiftDifference
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SquareRimComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorDomain
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2→ℝ)
local notation "V3" => (Fin 3→ℝ)
local notation "D2" => closedBall (0:V2) 1
local notation "Q2" => sphere (0:V2) 1

theorem HamiltonMarkedProtectedBall.no_detected_lattice_crossing_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ→ℝ)} [DiscreteTopology L]
    {e : α→OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos:0<Fintype.card ι)
    (v:κ→ℝ) (hv:v∈L) (hv0:v≠0) (hlen:3<‖v‖)
    (F:C(D2,(κ→ℝ)⧸L.toAddSubgroup))
    (hmid:∀x:Q2, x.val 0= -1 → |x.val 1|≤(‖v‖-3)/(‖v‖-2) →
      F ⟨x,sphere_subset_closedBall x.property⟩=QuotientAddGroup.mk
        ((‖v‖⁻¹+(1-2*‖v‖⁻¹)*((x.val 1+1)/2)) • v))
    (hrest:∀x:Q2, ¬(x.val 0= -1 ∧ |x.val 1|<(‖v‖-3)/(‖v‖-2)) →
      F ⟨x,sphere_subset_closedBall x.property⟩ ∈
        (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup) ''
          closedBall (0:κ→ℝ) (3/2)) : False := by
  classical
  let c:ℝ:=(‖v‖-3)/(‖v‖-2)
  have hn:0<‖v‖:=norm_pos_iff.mpr hv0
  have hd2:0<‖v‖-2:=by linarith
  have hc0:0<c:=div_pos (by linarith) hd2
  have hc1:c<1:=(div_lt_one hd2).mpr (by linarith)
  let J:=Icc (-c) c
  let C:=Q2 \ {z:V2 | z 0= -1 ∧ -c<z 1 ∧ z 1<c}
  have hCpre:IsPreconnected C:=isPreconnected_square_rim_complement_segment
    (by linarith) (by linarith) hc1
  obtain ⟨hCa,hCb⟩ := endpoints_mem_square_rim_complement_segment
    (a:= -c) (b:=c) (by linarith) (by linarith) hc1
  let : PreconnectedSpace C:=isPreconnected_iff_preconnectedSpace.mp hCpre
  let : PreconnectedSpace J:=isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let : ContractibleSpace D2:=(convex_closedBall (0:V2) 1).contractibleSpace
    ⟨0,mem_closedBall_self (by norm_num)⟩
  let : LocallyPathConnectedSpace D2:=(convex_closedBall (0:V2) 1).locallyPathConnectedSpace
  have hp: IsCoveringMap (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup):=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm DiscreteTopology.isDiscrete).isCoveringMap
  let zero:D2:=⟨0,mem_closedBall_self (by norm_num)⟩
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (F zero)
  obtain ⟨g,⟨_,hg⟩,_⟩ := hp.existsUnique_continuousMap_lifts F zero z hz
  have hgval(x:D2): (QuotientAddGroup.mk (g x):(κ→ℝ)⧸L.toAddSubgroup)=F x:=congrFun hg x
  obtain ⟨H,hH,hHinv,_⟩ := b.exists_attaching_disk_parametrization hpos
  have haQ(t:J):(![-1,(t:ℝ)]:V2)∈Q2 := by
    rw [mem_sphere_zero_iff_norm]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro i
      fin_cases i
      · norm_num
      · change |(t:ℝ)|≤1
        exact abs_le.mpr ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
    · have hh:=norm_le_pi_norm (![-1,(t:ℝ)]:V2) 0
      norm_num at hh
      exact hh
  let a:C(J,D2):=⟨fun t=>⟨![-1,(t:ℝ)],sphere_subset_closedBall (haQ t)⟩,by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩
  let model:C(J,κ→ℝ):=⟨fun t=>(‖v‖⁻¹+(1-2*‖v‖⁻¹)*(((t:ℝ)+1)/2)) • v,by fun_prop⟩
  have hmodel(t:J): (QuotientAddGroup.mk ((g.comp a) t):(κ→ℝ)⧸L.toAddSubgroup)=
      QuotientAddGroup.mk (model t) := by
    rw [ContinuousMap.comp_apply,hgval]
    exact hmid ⟨![-1,(t:ℝ)],haQ t⟩ rfl (abs_le.mpr t.property)
  let ca:C:=⟨![-1,-c],hCa⟩
  let cb:C:=⟨![-1,c],hCb⟩
  let ja:J:=⟨-c,show -c∈Icc (-c) c from ⟨le_rfl,by linarith⟩⟩
  let jb:J:=⟨c,show c∈Icc (-c) c from ⟨by linarith,le_rfl⟩⟩
  have hdiffA:=quotient_lift_endpoint_difference L (g.comp a) model hmodel ja jb
  let inc:C(C,D2):=⟨fun x=>⟨x,sphere_subset_closedBall x.property.1⟩,by fun_prop⟩
  have hCimage(x:C): F (inc x)∈
      (QuotientAddGroup.mk : (κ→ℝ)→(κ→ℝ)⧸L.toAddSubgroup) ''
        closedBall (0:κ→ℝ) (3/2) := by
    apply hrest ⟨x,x.property.1⟩
    intro hh
    exact x.property.2 ⟨hh.1,(abs_lt.mp hh.2).1,(abs_lt.mp hh.2).2⟩
  let canon:C(C,κ→ℝ):=⟨fun x=>(H.symm ⟨F (inc x),hCimage x⟩).val,by fun_prop⟩
  have hcanon(x:C): (QuotientAddGroup.mk ((g.comp inc) x):(κ→ℝ)⧸L.toAddSubgroup)=
      QuotientAddGroup.mk (canon x) :=
        (hgval (inc x)).trans (hHinv ⟨F (inc x),hCimage x⟩).symm
  have hdiffC:=quotient_lift_endpoint_difference L (g.comp inc) canon hcanon ca cb
  let u:κ→ℝ:=((3/2:ℝ)/‖v‖) • v
  have hu:u∈closedBall (0:κ→ℝ) (3/2) := by
    rw [mem_closedBall_zero_iff]
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (by norm_num) hn),div_mul_cancel₀ _ (ne_of_gt hn)]
  have hnu:-u∈closedBall (0:κ→ℝ) (3/2) := by
    simpa only [mem_closedBall_zero_iff,norm_neg] using hu
  have hthetaA:‖v‖⁻¹+(1-2*‖v‖⁻¹)*((-c+1)/2)=(3/2)/‖v‖ := by
    dsimp [c]
    field_simp
    ring
  have hthetaB:‖v‖⁻¹+(1-2*‖v‖⁻¹)*((c+1)/2)=1-(3/2)/‖v‖ := by
    dsimp [c]
    field_simp
    ring
  have hmodelA:model ja=u := by dsimp [model,ja]; rw [hthetaA]
  have hmodelB:model jb=v-u := by
    change (‖v‖⁻¹+(1-2*‖v‖⁻¹)*((c+1)/2)) • v=v-u
    rw [hthetaB]
    dsimp [u]
    module
  have hcanonA:canon ca=u := by
    have hval:F (inc ca)=QuotientAddGroup.mk u :=
      (hgval (inc ca)).symm.trans ((hmodel ja).trans (congrArg QuotientAddGroup.mk hmodelA))
    have heq:H.symm ⟨F (inc ca),hCimage ca⟩=⟨u,hu⟩ := by
      apply H.injective
      apply Subtype.ext
      simpa only [H.apply_symm_apply] using hval.trans (hH ⟨u,hu⟩).symm
    exact congrArg Subtype.val heq
  have hcanonB:canon cb= -u := by
    have hquot:(QuotientAddGroup.mk (v-u):(κ→ℝ)⧸L.toAddSubgroup)=QuotientAddGroup.mk (-u) := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa only [sub_neg_eq_add,sub_add_cancel] using (show v∈L.toAddSubgroup from hv)
    have hval:F (inc cb)=QuotientAddGroup.mk (-u) :=
      (hgval (inc cb)).symm.trans ((hmodel jb).trans
        ((congrArg QuotientAddGroup.mk hmodelB).trans hquot))
    have heq:H.symm ⟨F (inc cb),hCimage cb⟩=⟨-u,hnu⟩ := by
      apply H.injective
      apply Subtype.ext
      simpa only [H.apply_symm_apply] using hval.trans (hH ⟨-u,hnu⟩).symm
    exact congrArg Subtype.val heq
  rw [hmodelA,hmodelB] at hdiffA
  rw [hcanonA,hcanonB] at hdiffC
  have hh:(v-u)-u=(-u)-u:=hdiffA.symm.trans hdiffC
  have hzv:v=0:=by linear_combination hh
  exact hv0 hzv

theorem HamiltonMarkedProtectedBall.exists_original_exterior_essential_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ→ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α→OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim:Fintype.card ι+Fintype.card κ=3) (hi:Fintype.card ι=1) :
    let E:=closure (latticeHandleDomain ι κ L \ D)
    ∃ (j:V2→LatticeHandleAmbient ι κ L) (rim:C(Q2,frontier E)),
      PolyhedralPLInCharts e j D2 ∧ Topology.IsEmbedding (fun x:D2=>j x) ∧ MapsTo j D2 E ∧
      (∀x:Q2, j x=(rim x:LatticeHandleAmbient ι κ L)) ∧
      (∀x:D2, j x∈frontier E ↔ x.val∈Q2) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  classical
  dsimp only
  let E:=closure (latticeHandleDomain ι κ L \ D)
  obtain ⟨v,f,gamma,F,hv,hv0,hlen,hfg,hmid,hrest⟩ :=
    b.exists_original_detected_exterior_disk he hdim hi
  have hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((Dehn.squareRimLoop.map gamma.continuous).map F.continuous)) ≠ 1 := by
    intro htrivial
    have hnull : (F.comp gamma).Nullhomotopic :=
      Dehn.nullhomotopic_of_squareRimLoop (F.comp gamma)
        (Path.Homotopic.Quotient.exact htrivial)
    obtain ⟨G,hG⟩ := hnull.exists_closedBall_extension (F.comp gamma)
    apply b.no_detected_lattice_crossing_disk (by omega) v hv hv0 hlen G
    · intro x hx ht
      rw [hG x]
      exact hmid x hx ht
    · intro x hx
      rw [hG x]
      exact hrest x hx
  obtain ⟨j,rim,hj,hji,hjE,hrim,hproper,himage⟩ :=
    Dehn.exists_marked_boundary_disk_with_essential_image e E
      (b.plDomain_closed_complement he hdim hi) (frontier E) subset_rfl
      (by simpa only [Subtype.coe_preimage_self] using (isOpen_univ : IsOpen (univ:Set (frontier E))))
      f gamma hfg F hessential
  refine ⟨j,rim,hj,hji,hjE,hrim,hproper,?_⟩
  intro hnull
  have hh : (Dehn.squareRimLoop.map rim.continuous).Homotopic (Path.refl (rim Dehn.squareRimBase)) :=
    Path.Homotopic.Quotient.exact hnull
  apply himage
  apply Path.Homotopic.Quotient.eq.mpr
  have href : (Path.refl (rim Dehn.squareRimBase)).map F.continuous =
      Path.refl (F (rim Dehn.squareRimBase)) := by ext t; rfl
  simpa only [href] using hh.map F

end PoincareConjecture.M76
