import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarSideUniqueness
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarUniformSide

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem endpoint_projection_injective_on_fixed_collar_side
    {X Y A Z : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y} (f : X → Y) (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K) (a : A)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (hcenterO : (W (a,⟨1/2,by norm_num,by norm_num⟩) : Y) ∈ O)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (p : Z → X) (η : Z → C(unitInterval,X))
    (hη : ∀ z, η z 0 = p z)
    (hstart : ∀ z, f (p z) = W (a,⟨1/2,by norm_num,by norm_num⟩))
    (hfinite : (f ⁻¹' {(W (a,⟨1/2,by norm_num,by norm_num⟩) : Y)}).Finite)
    (hinto : ∀ z (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      η z t ∈ D ∧ f (η z t) ∈ connectedComponentIn (M \ S) y₀)
    (side : Z → Bool)
    (ε : Z → ℝ) (hε : ∀ z, 0 < ε z)
    (hside : ∀ z (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < ε z →
      ∀ q : A × unitInterval, (W q : Y) = f (η z t) →
        if side z then 1/2 < (q.2 : ℝ) else (q.2 : ℝ) < 1/2) :
    ∀ z w, side z = side w → p z = p w := by
  intro z w hzw
  have hside :=
    endpoint_eq_of_same_original_collar_side f hf H hH W a hO hOK hOM hcenter
      hcenterO y₀ hcover (fun b => if b then η w else η z)
      (fun b => by
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          simpa only [hη z] using hstart z
        · simp only [ite_true]
          simpa only [hη w] using hstart w)
      (by
        simp only [Bool.false_eq_true, ite_false, hη z, hstart z]
        exact hfinite)
      (fun b t ht ht1 => by
        cases b
        · exact hinto z t ht (ht1.trans (by norm_num))
        · exact hinto w t ht (ht1.trans (by norm_num)))
      (min (ε z) (ε w)) (lt_min (hε z) (hε w)) (side z)
      (by
        intro b t ht hte q hq
        cases b
        · exact hside z t ht (hte.trans_le (min_le_left _ _)) q hq
        · rw [hzw]
          exact hside w t ht (hte.trans_le (min_le_right _ _)) q hq)
  rw [← hη z, ← hη w]
  exact hside

theorem exists_endpoint_projection_injective_neighborhood
    {P X Y A : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y} (f : X → Y) (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (Γ : C(P × unitInterval,X))
    (hzero : ∀ p, f (Γ (p,0)) ∈ S)
    (hfinite : ∀ p, (f ⁻¹' {f (Γ (p,0))}).Finite)
    (hinto : ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (p,t) ∈ D ∧ f (Γ (p,t)) ∈ connectedComponentIn (M \ S) y₀)
    (hinj : Function.Injective (fun p => Γ (p,0)))
    (p : P) (hp : f (Γ (p,0)) ∈ O) :
    ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ InjOn (fun q => f (Γ (q,0))) V := by
  let Γ' : C(P × unitInterval,Y) := ⟨fun z => f (Γ z),hf.comp Γ.continuous⟩
  obtain ⟨V,ε,positive,hV,hpV,hε,_hεhalf,hnear,hside⟩ :=
    exists_endpoint_neighborhood_collar_side W hO hOK hcenter Γ'
      (fun q t ht ht1 => (connectedComponentIn_subset (M \ S) y₀ (hinto q t ht ht1).2).2)
      p hp
  refine ⟨V,hV,hpV,?_⟩
  intro q hq w hw hqw
  have hqO : f (Γ (q,0)) ∈ O := hnear q hq 0 hε
  let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  let z := W.symm ⟨f (Γ (q,0)),hOK hqO⟩
  have hz : z.2 = m := by
    apply Subtype.ext
    apply (hcenter z).mp
    simpa only [z,W.apply_symm_apply] using hzero q
  have hWq : (W (z.1,m) : Y) = f (Γ (q,0)) := by
    rw [← hz]
    exact congrArg Subtype.val (W.apply_symm_apply _)
  let η (v : P) : C(unitInterval,X) :=
    ⟨fun t => Γ (v,t),Γ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let paths (b : Bool) := if b then η w else η q
  have hstart (b : Bool) : f (paths b 0) = W (z.1,m) := by
    cases b
    · exact hWq.symm
    · exact hqw.symm.trans hWq.symm
  apply hinj
  exact endpoint_eq_of_same_original_collar_side f hf H hH W z.1 hO hOK hOM
    hcenter (hWq.symm ▸ hqO) y₀ hcover paths hstart (hfinite q)
    (by
      intro b t ht ht1
      cases b
      · exact hinto q t ht (ht1.trans (by norm_num))
      · exact hinto w t ht (ht1.trans (by norm_num)))
    ε hε positive (by
      intro b t ht hte v hv
      cases b
      · exact hside q hq t ht hte v hv
      · exact hside w hw t ht hte v hv)

end PoincareConjecture.M76.PrismBelt
