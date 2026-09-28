import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedCutOfOriginalCollars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalEndpointBallAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFiniteSphereCollar
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_sphere_cut_with_original_collars
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ d : MarkedSphereCut e R κ, d.spheres = S ∧
      (∀ i, IsCompact (closure (d.collar i)) ∧ IsConnected (closure (d.collar i)) ∧
        closure (d.collar i) ⊆ U) ∧
      (∀ i, Nonempty (OriginalFiniteSphereCollar e R (S i) (d.collar i)
        (fun b => d.ports (i,b)))) ∧
      ∀ (b : κ × Bool) (A : Set X), ChartwisePLBall e A (d.ports b) →
        A ⊆ d.carrier → ∃ A', Nonempty (ChartwisePLBall e A' (S b.1)) ∧
          A ⊆ interior A' ∧ A' ⊆ A ∪ closure (d.collar b.1) ∧ A' ⊆ R := by
  classical
  obtain ⟨t, N, HB, c, ε, Q, B, H, sB, hpiece, hclosedDis, hBval, hHval, hBdis,
    _, hQeq, _, hQPL, _, hQf, _⟩ :=
    exists_original_finite_pl_sphere_cut S sS hdis hR he hSR hU hSU
  have hεle (i : κ) : ε i ≤ 1 := by linarith [(hpiece i).2.2.2.2.2.1]
  obtain ⟨d, hdS, hdO, hdB, _⟩ := exists_marked_sphere_cut_of_original_collars
    (fun i => t i → ℝ × V3) S sS hdis hSR hR N (fun i => (hpiece i).1) HB c
    (fun i => (hpiece i).2.1) (fun i => (hpiece i).2.2.1)
    (fun i => (hpiece i).2.2.2.1) ε (fun i => (hpiece i).2.2.2.2.1) hεle
    (fun i => (hpiece i).2.2.2.2.2.2.1)
    (fun i => (hpiece i).2.2.2.2.2.2.2.2.2.trans inter_subset_right)
    hclosedDis B H sB hHval hBdis (hQeq ▸ hQPL) (hQeq ▸ hQf)
  have hclosure (i : κ) : closure (d.collar i) =
      c i '' ((N i).space ×ˢ Icc (-ε i) (ε i)) := by
    rw [hdO]
    exact (hpiece i).2.2.2.2.2.2.2.2.1
  refine ⟨d, hdS, ?_, ?_, ?_⟩
  · intro i
    rw [hclosure]
    have hNconn : IsConnected (N i).space := isConnected_iff_connectedSpace.mpr
      ((HB i).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp (sS i).isConnected))
    have hprod := hNconn.prod (isConnected_Icc (show -ε i ≤ ε i by
      linarith [(hpiece i).2.2.2.2.1]))
    refine ⟨(hpiece i).2.2.2.2.2.2.2.1, hprod.image (c i) ?_,
      (hpiece i).2.2.2.2.2.2.2.2.2.trans inter_subset_left⟩
    apply (hpiece i).2.1.continuousOn.mono
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    exact ⟨hx, by constructor <;> linarith [hr.1, hr.2, hεle i]⟩
  · intro i
    rw [hdO, hdB]
    exact ⟨{
      parameters := t i
      complex := N i
      finite := (hpiece i).1
      parametrization := HB i
      map := c i
      width := ε i
      width_pos := (hpiece i).2.2.2.2.1
      width_le := (hpiece i).2.2.2.2.2.1
      pl := (hpiece i).2.1
      embedding := (hpiece i).2.2.1
      center := (hpiece i).2.2.2.1
      open_eq := rfl
      closed_eq := (hpiece i).2.2.2.2.2.2.2.2.1
      isOpen := (hpiece i).2.2.2.2.2.2.1
      closedInterior := (hpiece i).2.2.2.2.2.2.2.2.2.trans inter_subset_right
      endpoint_eq := fun b => hBval (i,b)
      endpointMap := fun b => H (i,b)
      endpoint_value := fun b => hHval (i,b) }⟩
  · intro b A ball hA
    have hball : ChartwisePLBall e A
        (c b.1 '' ((N b.1).space ×ˢ {if b.2 then ε b.1 else -ε b.1})) := by
      rw [hdB, hBval] at ball
      exact ball
    have hA' : A ⊆ R \ c b.1 '' ((N b.1).space ×ˢ Ioo (-ε b.1) (ε b.1)) := by
      intro x hx
      have h := hA hx
      change x ∈ R \ ⋃ i, d.collar i at h
      rw [hdO] at h
      exact ⟨h.1, fun hxO => h.2 (mem_iUnion.mpr ⟨b.1, hxO⟩)⟩
    obtain ⟨hnew, hAint, hnewR⟩ := hball.attach_original_endpoint_half_strip
      he.cover he.compatible (N b.1) (hpiece b.1).1 (HB b.1) (c b.1)
      (hpiece b.1).2.1 (hpiece b.1).2.2.1 (hpiece b.1).2.2.2.1
      (hpiece b.1).2.2.2.2.1 (hεle b.1) b.2 hA'
      ((hpiece b.1).2.2.2.2.2.2.2.2.2.trans (inter_subset_right.trans interior_subset))
    refine ⟨_, hnew, hAint, ?_, hnewR⟩
    apply union_subset_union_right
    rw [hclosure]
    apply image_mono (prod_mono Subset.rfl ?_)
    intro r hr
    have hpos := (hpiece b.1).2.2.2.2.1
    cases hb : b.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, mem_Icc] at hr ⊢ <;>
      constructor <;> linarith [hr.1, hr.2]

theorem exists_marked_sphere_cut_with_endpoint_transfer
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ d : MarkedSphereCut e R κ, d.spheres = S ∧
      (∀ i, IsCompact (closure (d.collar i)) ∧ IsConnected (closure (d.collar i)) ∧
        closure (d.collar i) ⊆ U) ∧
      ∀ (b : κ × Bool) (A : Set X), ChartwisePLBall e A (d.ports b) →
        A ⊆ d.carrier → ∃ A', Nonempty (ChartwisePLBall e A' (S b.1)) ∧
          A ⊆ interior A' ∧ A' ⊆ A ∪ closure (d.collar b.1) ∧ A' ⊆ R := by
  obtain ⟨d, hS, hN, _, htransfer⟩ :=
    exists_marked_sphere_cut_with_original_collars S sS hdis hR he hSR hU hSU
  exact ⟨d, hS, hN, htransfer⟩

end PoincareConjecture.M76
