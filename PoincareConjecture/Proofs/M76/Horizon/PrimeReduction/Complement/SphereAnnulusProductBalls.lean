import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRetainedDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnularDiskProductBall









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_sphere_annulus_product_balls
    {band : Set V3} (c : Annulus ≃ₜ band) (hc : c.IsFinitePL)
    (hband : band ⊆ Sphere) (p : Sphere) (hp : (p : V3) ∉ band) :
    ∃ (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ)),
      (∀ b, q b = (fun z : Annulus => (c z : V3)) ''
        {z | depth 8 z = if b then 1 else -1}) ∧
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        k b ∩ band = q b) ∧
      Disjoint (k true) (k false) ∧ (k true ∪ k false) ∪ band = Sphere ∧
      ∀ b,
        let A := Sphere \ (k b \ q b)
        IsFinitePLBallPair P2 A (q b) ∧ k (!b) ∪ band = A ∧
        C b = ((q b ×ˢ I) ∪ (A ×ˢ ({0, 1} : Set ℝ))) \
          ((A ×ˢ {(1 : ℝ)}) \ (q b ×ˢ {(1 : ℝ)})) ∧
        IsFinitePLBallPair P2 (C b) (q b ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P2 (k (!b) ×ˢ {(1 : ℝ)}) (q (!b) ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P3 (A ×ˢ I)
          ((band ×ˢ {(1 : ℝ)}) ∪ (C b ∪ (k (!b) ×ˢ {(1 : ℝ)}))) ∧
        C b ∩ (band ×ˢ {(1 : ℝ)}) = q b ×ˢ {(1 : ℝ)} ∧
        (k (!b) ×ˢ {(1 : ℝ)}) ∩ (band ×ˢ {(1 : ℝ)}) = q (!b) ×ˢ {(1 : ℝ)} ∧
        Disjoint (k (!b) ×ˢ {(1 : ℝ)}) (C b) := by
  classical
  obtain ⟨k,hk,hdis,hcover⟩ := exists_unitCube_sphere_annulus_retained_disks c hc hband p hp
  let q := fun b : Bool => (fun z : Annulus => (c z : V3)) ''
    {z | depth 8 z = if b then 1 else -1}
  have hdis' (b : Bool) : Disjoint (k b) (k (!b)) := by
    cases b
    · exact hdis.symm
    · exact hdis
  have hqband (b : Bool) : q b ⊆ band := by
    dsimp only [q]
    rw [← (hk b).2.2]
    exact inter_subset_right
  have hA (b : Bool) : IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b) := by
    obtain ⟨K,hK,hKS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
    have hfront : Sphere = frontier (closedBall (0 : V3) 1) :=
      (frontier_closedBall _ one_ne_zero).symm
    obtain ⟨x,hx,_⟩ := (hk (!b)).1.sdiff_nonempty
    have hout : (frontier (closedBall (0 : V3) 1) \ k b).Nonempty :=
      ⟨x,hfront.subset ((hk (!b)).2.1 hx),
        fun h => disjoint_left.mp (hdis' b) h hx⟩
    have h := K.isFinitePLBallPair_convex_sphere_disk_complement hK
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKS.trans hfront) (by simp) (hk b).1 ((hk b).2.1.trans hfront.subset) hout
    rwa [← hfront] at h
  have hAeq (b : Bool) : k (!b) ∪ band = Sphere \ (k b \ q b) := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact ⟨(hk (!b)).2.1 hx,fun h => disjoint_left.mp (hdis' b) h.1 hx⟩
      · exact ⟨hband hx,fun h => h.2 ((hk b).2.2.subset ⟨h.1,hx⟩)⟩
    · rintro x ⟨hxS,hx⟩
      have hxcover := hcover.symm.subset hxS
      by_cases hxb : x ∈ k b
      · exact Or.inr (hqband b (by by_contra hn; exact hx ⟨hxb,hn⟩))
      · cases b <;> simp only [Bool.not_false,Bool.not_true,mem_union] at hxcover ⊢ <;> tauto
  have hproducts (b : Bool) := (hA b).product_with_annular_top (hk (!b)).1
    (hAeq b) (hk (!b)).2.2 (hqband b)
    ((hdis' b).mono_left (hk b).1.1)
  choose C hCeq hC htop hprod hmeet htopmeet hcapdis using hproducts
  exact ⟨k,q,C,fun _ => rfl,hk,hdis,hcover,
    fun b => ⟨hA b,hAeq b,hCeq b,hC b,htop b,hprod b,hmeet b,htopmeet b,hcapdis b⟩⟩

end PoincareConjecture.M76
