import PEqualNP.Defs

-- The witness has thirteen binary gates. Any circuit with a NOT and fewer gates
-- would have at most eleven binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12128_aux
namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.and,[5,2]⟩, ⟨.or,[6,7]⟩, ⟨.and,[4,9]⟩, ⟨.or,[0,1]⟩, ⟨.or,[3,8]⟩, ⟨.or,[5,2]⟩, ⟨.and,[10,13]⟩, ⟨.or,[4,9]⟩, ⟨.and,[11,12]⟩, ⟨.or,[14,16]⟩, ⟨.and,[15,17]⟩],18⟩

theorem size : witness.size = 13 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfee8e880fe80e800
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfee8e880fe80e800 : W) 11 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 11 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfee8e880fe80e800 : BitVec 64) 11 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def ew0 : Word := 0x8800

def ew1 : Word := 0xa000

def ew2 : Word := 0xaa00

def ew3 : Word := 0xaaaa

def ew4 : Word := 0xc000

def ew5 : Word := 0xcc00

def ew6 : Word := 0xcccc

def ew7 : Word := 0xf000

def ew8 : Word := 0xf0f0

def ew9 : Word := 0xff00

def ew10 : Word := 0x2a2a00

def ew11 : Word := 0x4c4c00

def ew12 : Word := 0x707000

def ew13 : Word := 0x808000

def ew14 : Word := 0x880088

def ew15 : Word := 0x888800

def ew16 : Word := 0xa000a0

def ew17 : Word := 0xa0a000

def ew18 : Word := 0xaa0000

def ew19 : Word := 0xaa0a00

def ew20 : Word := 0xaa2200

def ew21 : Word := 0xaa2a00

def ew22 : Word := 0xaaaa00

def ew23 : Word := 0xc0c000

def ew24 : Word := 0xcc0000

def ew25 : Word := 0xcc0c00

def ew26 : Word := 0xcc4400

def ew27 : Word := 0xcc4c00

def ew28 : Word := 0xcccc00

def ew29 : Word := 0xf00000

def ew30 : Word := 0xf03000

def ew31 : Word := 0xf05000

def ew32 : Word := 0xf07000

def ew33 : Word := 0xf0f000

def ew34 : Word := 0xff0000

def ew35 : Word := 0xff8000

def ew36 : Word := 0xff8800

def ew37 : Word := 0xffa000

def ew38 : Word := 0xffc000

def ew39 : Word := 0x8800880

def ew40 : Word := 0xa000a00

def ew41 : Word := 0xa0a0a0a

def ew42 : Word := 0xaa00000

def ew43 : Word := 0xaa00aa0

def ew44 : Word := 0xc0c0c0c

def ew45 : Word := 0xcc00cc0

def ew46 : Word := 0xf000f00

def ew47 : Word := 0xf0f0000

def ew48 : Word := 0xff00000

def ew49 : Word := 0x20802080

def ew50 : Word := 0x22002200

def ew51 : Word := 0x22222222

def ew52 : Word := 0x22880000

def ew53 : Word := 0x22882288

def ew54 : Word := 0x30303030

def ew55 : Word := 0x30c030c0

def ew56 : Word := 0x33003300

def ew57 : Word := 0x33330000

def ew58 : Word := 0x33cc0000

def ew59 : Word := 0x44444444

def ew60 : Word := 0x44884488

def ew61 : Word := 0x50505050

def ew62 : Word := 0x50a050a0

def ew63 : Word := 0x55005500

def ew64 : Word := 0x55550000

def ew65 : Word := 0x55aa0000

def ew66 : Word := 0x80800808

def ew67 : Word := 0x80802020

def ew68 : Word := 0x80808080

def ew69 : Word := 0x82008200

def ew70 : Word := 0x82820000

def ew71 : Word := 0x88002200

def ew72 : Word := 0x88880000

def ew73 : Word := 0x88888888

def ew74 : Word := 0xa0000a00

def ew75 : Word := 0xa0a00000

def ew76 : Word := 0xa0a0a0a0

def ew77 : Word := 0xa8a8a8a8

def ew78 : Word := 0xaa00aa00

def ew79 : Word := 0xaaaa0000

def ew80 : Word := 0xaaaa8888

def ew81 : Word := 0xaaaaa0a0

def ew82 : Word := 0xaaaaaaaa

def ew83 : Word := 0xc0c0c0c0

def ew84 : Word := 0xcc00cc00

def ew85 : Word := 0xcccc0000

def ew86 : Word := 0xcccccccc

def ew87 : Word := 0xeaeac0c0

def ew88 : Word := 0xececa0a0

def ew89 : Word := 0xf000f000

def ew90 : Word := 0xf0f00000

def ew91 : Word := 0xf0f0f0f0

def ew92 : Word := 0xf8f88888

def ew93 : Word := 0xff000000

def ew94 : Word := 0xff00ff00

def ew95 : Word := 0xffff0000

def ew96 : Word := 0xaa0000aa00

def ew97 : Word := 0xcc0000cc00

def ew98 : Word := 0xf00000f000

def ew99 : Word := 0xff00000000

def ew100 : Word := 0x888800000000

def ew101 : Word := 0x888800002222

def ew102 : Word := 0x888800004444

def ew103 : Word := 0x888800008888

def ew104 : Word := 0xa0a000000000

def ew105 : Word := 0xa0a000005050

def ew106 : Word := 0xa0a00000a0a0

def ew107 : Word := 0xaa0000000000

def ew108 : Word := 0xaa0000005500

def ew109 : Word := 0xaa000000aa00

def ew110 : Word := 0xaaaa00000000

def ew111 : Word := 0xaaaa0000aaaa

def ew112 : Word := 0xc0c000003030

def ew113 : Word := 0xcc0000003300

def ew114 : Word := 0xcccc00000000

def ew115 : Word := 0xcccc0000cccc

def ew116 : Word := 0xf0f000000000

def ew117 : Word := 0xf0f00000f0f0

def ew118 : Word := 0xff0000000000

def ew119 : Word := 0xff000000ff00

def ew120 : Word := 0xffff00000000

def ew121 : Word := 0xa000a0a000a00

def ew122 : Word := 0xc000c0c000c00

def ew123 : Word := 0xf00000f000000

def ew124 : Word := 0xf000f00000000

def ew125 : Word := 0x22002222002200

def ew126 : Word := 0x30003030003000

def ew127 : Word := 0x33000033000000

def ew128 : Word := 0x33003300000000

def ew129 : Word := 0x88008800880088

def ew130 : Word := 0xa000a000a000a0

def ew131 : Word := 0xaa000000aa0000

def ew132 : Word := 0xaa00aa00000000

def ew133 : Word := 0xaa00aa00aa00aa

def ew134 : Word := 0xaa00aaaa00aa00

def ew135 : Word := 0xc000c000c000c0

def ew136 : Word := 0xcc000000cc0000

def ew137 : Word := 0xcc00cc00000000

def ew138 : Word := 0xcc00cc00cc00cc

def ew139 : Word := 0xcc00cccc00cc00

def ew140 : Word := 0xf0000000f00000

def ew141 : Word := 0xf000f000000000

def ew142 : Word := 0xf000f000f000f0

def ew143 : Word := 0xf000f0f000f000

def ew144 : Word := 0xff000000000000

def ew145 : Word := 0xff000000ff0000

def ew146 : Word := 0xff0000ff000000

def ew147 : Word := 0xff00ff00000000

def ew148 : Word := 0x808080804040404

def ew149 : Word := 0x808080808080808

def ew150 : Word := 0xa000a0005000500

def ew151 : Word := 0xa000a000a000a00

def ew152 : Word := 0xa0a000005050000

def ew153 : Word := 0xa0a00000a0a0000

def ew154 : Word := 0xa0a0a0a00000000

def ew155 : Word := 0xa0a0a0a0a0a0a0a

def ew156 : Word := 0xc0c0c0c0c0c0c0c

def ew157 : Word := 0xf000f000f000f00

def ew158 : Word := 0xf0f00000f0f0000

def ew159 : Word := 0xf0f0f0f00000000

def ew160 : Word := 0x2020202010101010

def ew161 : Word := 0x2020202020202020

def ew162 : Word := 0x2200220011001100

def ew163 : Word := 0x2200220022002200

def ew164 : Word := 0x2222000011110000

def ew165 : Word := 0x2222000022220000

def ew166 : Word := 0x2222222200000000

def ew167 : Word := 0x2222222222222222

def ew168 : Word := 0x3030303030303030

def ew169 : Word := 0x3300330033003300

def ew170 : Word := 0x3333000033330000

def ew171 : Word := 0x3333333300000000

def ew172 : Word := 0x4444444444444444

def ew173 : Word := 0x5050505050505050

def ew174 : Word := 0x5500550055005500

def ew175 : Word := 0x5555000055550000

def ew176 : Word := 0x5555555500000000

def ew177 : Word := 0x8080080880800808

def ew178 : Word := 0x8080202080802020

def ew179 : Word := 0x8080808080808080

def ew180 : Word := 0x8200820082008200

def ew181 : Word := 0x8282000082820000

def ew182 : Word := 0x8282828200000000

def ew183 : Word := 0x8800220088002200

def ew184 : Word := 0x8800880044004400

def ew185 : Word := 0x8800880088008800

def ew186 : Word := 0x8888000088880000

def ew187 : Word := 0x8888222200000000

def ew188 : Word := 0x8888888800000000

def ew189 : Word := 0x8888888822222222

def ew190 : Word := 0x8888888844444444

def ew191 : Word := 0x8888888888888888

def ew192 : Word := 0xa0000a00a0000a00

def ew193 : Word := 0xa000a00050005000

def ew194 : Word := 0xa000a000a000a000

def ew195 : Word := 0xa0a00000a0a00000

def ew196 : Word := 0xa0a00a0a00000000

def ew197 : Word := 0xa0a0a0a000000000

def ew198 : Word := 0xa0a0a0a00a0a0a0a

def ew199 : Word := 0xa0a0a0a050505050

def ew200 : Word := 0xa0a0a0a0a0a0a0a0

def ew201 : Word := 0xa8a8a8a8a8a8a8a8

def ew202 : Word := 0xaa00000055000000

def ew203 : Word := 0xaa000000aa000000

def ew204 : Word := 0xaa00aa0000000000

def ew205 : Word := 0xaa00aa0055005500

def ew206 : Word := 0xaa00aa00aa00aa00

def ew207 : Word := 0xaaaa000000000000

def ew208 : Word := 0xaaaa000055550000

def ew209 : Word := 0xaaaa0000aaaa0000

def ew210 : Word := 0xaaaa8888aaaa8888

def ew211 : Word := 0xaaaaa0a0aaaaa0a0

def ew212 : Word := 0xaaaaaaaa00000000

def ew213 : Word := 0xaaaaaaaaaaaaaaaa

def ew214 : Word := 0xc0c0c0c00c0c0c0c

def ew215 : Word := 0xc0c0c0c030303030

def ew216 : Word := 0xc0c0c0c0c0c0c0c0

def ew217 : Word := 0xcc00cc0033003300

def ew218 : Word := 0xcc00cc00cc00cc00

def ew219 : Word := 0xcccc000033330000

def ew220 : Word := 0xcccc0000cccc0000

def ew221 : Word := 0xcccccccc00000000

def ew222 : Word := 0xcccccccccccccccc

def ew223 : Word := 0xeaeac0c0eaeac0c0

def ew224 : Word := 0xececa0a0ececa0a0

def ew225 : Word := 0xf000f0000f000f00

def ew226 : Word := 0xf000f000f000f000

def ew227 : Word := 0xf0f000000f0f0000

def ew228 : Word := 0xf0f00000f0f00000

def ew229 : Word := 0xf0f0f0f000000000

def ew230 : Word := 0xf0f0f0f0f0f0f0f0

def ew231 : Word := 0xf8f88888f8f88888

def ew232 : Word := 0xff000000ff000000

def ew233 : Word := 0xff00ff0000000000

def ew234 : Word := 0xff00ff00ff00ff00

def ew235 : Word := 0xffff000000000000

def ew236 : Word := 0xffff0000ffff0000

def ew237 : Word := 0xffffffff00000000

def ew238 : Word := 0xffffffffff00ff00

def labelsBlock0 : Array Nat := #[
  0xb24,
  0xb0c,
  0xd24,
  0x271c,
  0xb28,
  0x171c,
  0x1924,
  0xd14,
  0xe28,
  0x334c,
  0xd30,
  0x174c,
  0xe30,
  0x1754,
  0x1758,
  0x1a28
]

def labelsBlock1 : Array Nat := #[
  0xe18,
  0x10c6,
  0x1944,
  0x3554,
  0xb20,
  0xe20,
  0xd20,
  0x10d2,
  0x1036,
  0xb04,
  0xb4c,
  0x278c,
  0xd04,
  0x10e6,
  0x2794,
  0x338c
]

def labelsBlock2 : Array Nat := #[
  0x1904,
  0x10be,
  0x10ee,
  0x3658,
  0x4100c6,
  0x4320c6,
  0x4200c6,
  0x4310c6,
  0x4210c6,
  0x4300c6,
  0x1092,
  0x1c30,
  0x10c2,
  0x7420d2,
  0x10f2,
  0x107a
]

def labelsBlock3 : Array Nat := #[
  0xd54,
  0xb08,
  0x1a60,
  0x2798,
  0x1032,
  0x1c60,
  0x270c,
  0x2b8c,
  0x2714,
  0x1960,
  0x3594,
  0x330c,
  0x7420e6,
  0x1002,
  0x1a48,
  0xb8c
]

def labelsBlock4 : Array Nat := #[
  0x109a,
  0x6210d2,
  0x7320d2,
  0x6200d2,
  0x4310d2,
  0x4300d2,
  0x4100d2,
  0x170c,
  0x1a20,
  0x1c20,
  0x2718,
  0x1714,
  0x33c4,
  0x1920,
  0x1052,
  0x10d6
]

def labelsBlock5 : Array Nat := #[
  0x1c50,
  0x4100be,
  0x4420be,
  0x4200be,
  0x4410be,
  0x4210be,
  0x6200e6,
  0x4400be,
  0xe58,
  0x35c4,
  0x4100e6,
  0x4300e6,
  0x6210e6,
  0x7420ee,
  0x7320e6,
  0x4310e6
]

def labelsBlock6 : Array Nat := #[
  0x1006,
  0x105a,
  0x3698,
  0x1056,
  0x4100ee,
  0x6210ee,
  0x6200ee,
  0x10a6,
  0x4310ee,
  0x4300ee,
  0x7320ee,
  0x10ba,
  0x100a,
  0x35d0,
  0x33c8,
  0x2b0c
]

def labelsBlock7 : Array Nat := #[
  0x36d0,
  0x36c8,
  0x10da,
  0x7430f2,
  0x7430c2,
  0x102a,
  0x4100f2,
  0x4200f2,
  0x4210f2,
  0x6320f2,
  0x6310f2,
  0x6300f2,
  0x105e,
  0x51007a,
  0x52007a,
  0x52107a
]

def labelsBlock8 : Array Nat := #[
  0xe08,
  0x1718,
  0x1a08,
  0x100e,
  0x61007a,
  0x71007a,
  0x62007a,
  0x72007a,
  0x62107a,
  0x72107a,
  0x10ae,
  0x41007a,
  0x42007a,
  0x3514,
  0x42107a,
  0x6320be
]

def labelsBlock9 : Array Nat := #[
  0x6320c2,
  0x1540310d2,
  0x7430be,
  0x6310be,
  0x6310c2,
  0x1544300d2,
  0x6300be,
  0x6300c2,
  0x154c100d2,
  0x4100c2,
  0x4200c2,
  0x4210c2,
  0x2ba4,
  0x10f6,
  0xb48,
  0xb44
]

def labelsBlock10 : Array Nat := #[
  0xd44,
  0x1108100be,
  0x1104200be,
  0x1084400be,
  0x2da4,
  0x14d4100e6,
  0x1454300e6,
  0x14401007a,
  0x14802007a,
  0x14842107a,
  0x10de,
  0x102e,
  0x10ca,
  0xe10,
  0x103a,
  0x5100ba
]

def labelsBlock11 : Array Nat := #[
  0x5300ba,
  0x5310ba,
  0x1062,
  0x4100ba,
  0x6100ba,
  0x7100ba,
  0x4300ba,
  0x6300ba,
  0x7300ba,
  0x4310ba,
  0x6310ba,
  0x7310ba,
  0x18c8100be,
  0x14d4100ee,
  0x10c8100c6,
  0x1d0c100be
]

def labelsBlock12 : Array Nat := #[
  0x7420d6,
  0x18c4200be,
  0x2ba8,
  0x10c4200c6,
  0x1d0c200be,
  0x1086300be,
  0x1106300be,
  0x110a300be,
  0x1084300c6,
  0x18c4400be,
  0x18c8400be,
  0x1d0c210be,
  0x110a310be,
  0x18c8410be,
  0xb00,
  0x1d08310d2
]

def labelsBlock13 : Array Nat := #[
  0x1d08300d2,
  0x1d08100d2,
  0xd10,
  0x1066,
  0x565108100be,
  0x565104200be,
  0x565084400be,
  0x3618,
  0x107e,
  0x10b6,
  0x1d08100e6,
  0x1d08300e6,
  0x41005a,
  0x42005a,
  0x43005a,
  0x42105a
]

def labelsBlock14 : Array Nat := #[
  0x43105a,
  0x43205a,
  0x2b28,
  0x5650c8100c6,
  0x5650c4200c6,
  0x565084300c6,
  0x1744,
  0xd94,
  0x1440100ba,
  0x14c0300ba,
  0x14c4310ba,
  0x1540310e6,
  0x1d08100ee,
  0xe00,
  0x1072,
  0x108e
]

def labelsBlock15 : Array Nat := #[
  0x2b24,
  0x4100d6,
  0x6210d6,
  0x6200d6,
  0xe48,
  0x1042,
  0x1082,
  0x2d24,
  0x1d08310e6,
  0x1cc8100d2,
  0x10c6200d2,
  0x1884300d2,
  0x2db0,
  0x2eb0,
  0x4310da,
  0x7320d6
]

def labelsBlock16 : Array Nat := #[
  0x2ea8,
  0x4310d6,
  0x4300d6,
  0x431032,
  0x430032,
  0x410032,
  0xe98,
  0x7420da,
  0x1540310ee,
  0x1d08310ee,
  0x1cc8100e6,
  0x10c6200e6,
  0x1454300ee,
  0x1d08300ee,
  0x1884300e6,
  0xd00
]

def labelsBlock17 : Array Nat := #[
  0xf1c,
  0x1b4c,
  0x1d54,
  0x1096,
  0x4100f6,
  0x6320f6,
  0x4420f6,
  0x7430f6,
  0x39a4,
  0x4200f6,
  0x6310f6,
  0x2d94,
  0x4410f6,
  0x4210f6,
  0x6300f6,
  0x2e98
]

def labelsBlock18 : Array Nat := #[
  0x4400f6,
  0xd50,
  0xe50,
  0x410052,
  0x430052,
  0x431052,
  0x1086,
  0x2d30,
  0x1d0c100f2,
  0x1cc8100ee,
  0x1d0c200f2,
  0x10c6200ee,
  0x1d0c210f2,
  0x1884300ee,
  0x1720,
  0x104a
]

def labelsBlock19 : Array Nat := #[
  0x103e,
  0x43002e,
  0x43102e,
  0x43202e,
  0x1076,
  0x2710,
  0x2708,
  0x3348,
  0x5420d2,
  0x1704,
  0xf24,
  0x1748,
  0x1750,
  0x1724,
  0xf0c,
  0x1b0c
]

def labelsBlock20 : Array Nat := #[
  0x1d14,
  0x410056,
  0x430056,
  0x431056,
  0x3308,
  0x3344,
  0x3544,
  0x18c8100f2,
  0x18c8100f6,
  0x2e30,
  0x1494100f2,
  0x1108100f6,
  0x1d0c100f6,
  0x18c4200f2,
  0x18c4200f6,
  0x2e28
]

def labelsBlock21 : Array Nat := #[
  0x1454200f2,
  0x1104200f6,
  0x1d0c200f6,
  0x1086300f2,
  0x1086300f6,
  0x1106300f6,
  0x110a300f6,
  0x1540210f2,
  0x1084400f6,
  0x18c4400f6,
  0x18c8400f6,
  0x1d0c210f6,
  0x110a310f6,
  0x18c8410f6,
  0x5420e6,
  0x2704
]

def labelsBlock22 : Array Nat := #[
  0x1c00,
  0x1a00,
  0x1700,
  0x2700,
  0x1728,
  0x101a,
  0x101e,
  0x1022,
  0x41002e,
  0x1046,
  0x620046,
  0x42002e,
  0x62003e,
  0x42102e,
  0x62103e,
  0x19c4
]

def labelsBlock23 : Array Nat := #[
  0x10b2,
  0x6210da,
  0x1d0c100c2,
  0x7320da,
  0x4100da,
  0x2d14,
  0x1d0c200c2,
  0x4100de,
  0x2e18,
  0x4300de,
  0x1c10,
  0x4310de,
  0x1d0c210c2,
  0x4300da,
  0x5420ee,
  0x1d
]

def labelsBlock24 : Array Nat := #[
  0x1730,
  0x25,
  0x9,
  0x19,
  0x49,
  0x45,
  0x81,
  0x7d,
  0x41005e,
  0x70204e,
  0x42005e,
  0x71204e,
  0x73204e,
  0x42105e,
  0x712046,
  0x732046
]

def labelsBlock25 : Array Nat := #[
  0x73203e,
  0x2b08,
  0x3550,
  0x3650,
  0x108a,
  0x742540310d2,
  0x7424d4100ee,
  0x565108100f6,
  0x171,
  0x10ce,
  0x3648,
  0x742544300d2,
  0x7424d4100e6,
  0x565104200f6,
  0x191,
  0x74254c100d2
]

def labelsBlock26 : Array Nat := #[
  0x742454300e6,
  0x565084400f6,
  0x1bd,
  0x7420de,
  0x5430f2,
  0x1900,
  0x1708,
  0x1710,
  0x3500,
  0x3504,
  0x3300,
  0x3304,
  0xf4c,
  0x21,
  0x29,
  0x2d
]

def labelsBlock27 : Array Nat := #[
  0x31,
  0x4d,
  0x51,
  0x55,
  0x65,
  0x69,
  0x85,
  0x89,
  0x99,
  0xb1c,
  0x1016,
  0x1012,
  0x41003e,
  0xe9,
  0x410046,
  0xf5
]

def labelsBlock28 : Array Nat := #[
  0x101,
  0x430046,
  0x43003e,
  0x41004e,
  0x43004e,
  0x43103e,
  0x43104e,
  0x431046,
  0x104e,
  0x125,
  0x139,
  0x14d,
  0x4100ca,
  0x6210ce,
  0x410062,
  0x169
]

def labelsBlock29 : Array Nat := #[
  0x7320ce,
  0x165,
  0x175,
  0x179,
  0x17d,
  0x4200ca,
  0x6200ce,
  0x420062,
  0x189,
  0x185,
  0x195,
  0x199,
  0x19d,
  0x4210ca,
  0x6200e2,
  0x4310ca
]

def labelsBlock30 : Array Nat := #[
  0x4320ca,
  0x1a5,
  0x1a9,
  0x1ad,
  0x421062,
  0x1b5,
  0x4300ca,
  0x1c1,
  0x1c5,
  0x1c9,
  0x1cd,
  0x10e2,
  0x1d5,
  0x1d9,
  0x1e1,
  0x1e9
]

def labelsBlock31 : Array Nat := #[
  0x1ed,
  0x1f9,
  0x3600,
  0x5,
  0xf28,
  0x15,
  0xb40,
  0xd40,
  0xe40,
  0xd,
  0x11,
  0xf54,
  0x41,
  0x39,
  0x3d,
  0x5d
]

def labelsBlock32 : Array Nat := #[
  0x61,
  0xf58,
  0x79,
  0x71,
  0x75,
  0x91,
  0x95,
  0xa1,
  0xa5,
  0x35,
  0x59,
  0x6d,
  0x8d,
  0x9d,
  0xa9,
  0xd1c
]

def labelsBlock33 : Array Nat := #[
  0xf14,
  0x1b44,
  0x1d44,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9,
  0xdd,
  0xe5
]

def labelsBlock34 : Array Nat := #[
  0xf1,
  0xfd,
  0xed,
  0xf9,
  0x105,
  0x109,
  0x10d,
  0x111,
  0xb88,
  0xb84,
  0xd84,
  0x1984,
  0x109e,
  0x10a2,
  0x10aa,
  0x129
]

def labelsBlock35 : Array Nat := #[
  0x12d,
  0x131,
  0x135,
  0x13d,
  0x141,
  0x145,
  0x149,
  0x151,
  0x155,
  0x159,
  0x15d,
  0x7310a6,
  0x403066,
  0x1d08310da,
  0x16d,
  0x4310ce
]

def labelsBlock36 : Array Nat := #[
  0x4100ea,
  0x7310ae,
  0x413066,
  0x1d08310d6,
  0x18d,
  0x4300ce,
  0x4100e2,
  0x6200da,
  0x6200ea,
  0x7320b6,
  0x41306a,
  0x1d08300d6,
  0x1b9,
  0x4100ce,
  0x4300e2,
  0x7320de
]

def labelsBlock37 : Array Nat := #[
  0x7320e2,
  0x6200de,
  0x6210ea,
  0x6210de,
  0x6210e2,
  0x10ea,
  0x181,
  0x1a1,
  0x1b1,
  0x1d1,
  0x1dd,
  0x1e5,
  0x1f1,
  0x1f5,
  0x1fd,
  0x201
]

def labelsBlock38 : Array Nat := #[
  0x205,
  0x209,
  0x1,
  0xad,
  0xe1,
  0x1026,
  0x115,
  0x106e,
  0x1740,
  0x119,
  0x11d,
  0x3900,
  0x2d00,
  0x2b00,
  0x121,
  0x161
]

def labelsBlock39 : Array Nat := #[
  0x20d
]

def labelsGet (i : Nat) : Nat :=
  if i < 320 then
    if i < 160 then
      if i < 80 then
        if i < 32 then
          if i < 16 then
            labelsBlock0.getD (i-0) 3
          else
            labelsBlock1.getD (i-16) 3
        else
          if i < 48 then
            labelsBlock2.getD (i-32) 3
          else
            if i < 64 then
              labelsBlock3.getD (i-48) 3
            else
              labelsBlock4.getD (i-64) 3
      else
        if i < 112 then
          if i < 96 then
            labelsBlock5.getD (i-80) 3
          else
            labelsBlock6.getD (i-96) 3
        else
          if i < 128 then
            labelsBlock7.getD (i-112) 3
          else
            if i < 144 then
              labelsBlock8.getD (i-128) 3
            else
              labelsBlock9.getD (i-144) 3
    else
      if i < 240 then
        if i < 192 then
          if i < 176 then
            labelsBlock10.getD (i-160) 3
          else
            labelsBlock11.getD (i-176) 3
        else
          if i < 208 then
            labelsBlock12.getD (i-192) 3
          else
            if i < 224 then
              labelsBlock13.getD (i-208) 3
            else
              labelsBlock14.getD (i-224) 3
      else
        if i < 272 then
          if i < 256 then
            labelsBlock15.getD (i-240) 3
          else
            labelsBlock16.getD (i-256) 3
        else
          if i < 288 then
            labelsBlock17.getD (i-272) 3
          else
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              labelsBlock19.getD (i-304) 3
  else
    if i < 480 then
      if i < 400 then
        if i < 352 then
          if i < 336 then
            labelsBlock20.getD (i-320) 3
          else
            labelsBlock21.getD (i-336) 3
        else
          if i < 368 then
            labelsBlock22.getD (i-352) 3
          else
            if i < 384 then
              labelsBlock23.getD (i-368) 3
            else
              labelsBlock24.getD (i-384) 3
      else
        if i < 432 then
          if i < 416 then
            labelsBlock25.getD (i-400) 3
          else
            labelsBlock26.getD (i-416) 3
        else
          if i < 448 then
            labelsBlock27.getD (i-432) 3
          else
            if i < 464 then
              labelsBlock28.getD (i-448) 3
            else
              labelsBlock29.getD (i-464) 3
    else
      if i < 560 then
        if i < 512 then
          if i < 496 then
            labelsBlock30.getD (i-480) 3
          else
            labelsBlock31.getD (i-496) 3
        else
          if i < 528 then
            labelsBlock32.getD (i-512) 3
          else
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              labelsBlock34.getD (i-544) 3
      else
        if i < 592 then
          if i < 576 then
            labelsBlock35.getD (i-560) 3
          else
            labelsBlock36.getD (i-576) 3
        else
          if i < 608 then
            labelsBlock37.getD (i-592) 3
          else
            if i < 624 then
              labelsBlock38.getD (i-608) 3
            else
              labelsBlock39.getD (i-624) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 10)) % 1024)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (10*q)) % 1024)

def viewsBlock0 : Array View := #[
  ⟨0xff00,⟨8,by decide⟩,0xe800,[ew2,ew5,ew7],3,decodeHints 0x98804000140081605414⟩,
  ⟨0xaaaa00,⟨9,by decide⟩,0x80a800,[ew15,ew17,ew18],3,decodeHints 0x0⟩,
  ⟨0xcccc00,⟨10,by decide⟩,0x80c800,[ew15,ew23,ew24],3,decodeHints 0x0⟩,
  ⟨0xf0f000,⟨12,by decide⟩,0x80e000,[ew17,ew23,ew29],3,decodeHints 0x0⟩,
  ⟨0xaa00aa0,⟨5,by decide⟩,0xa800800,[ew39,ew40,ew42],3,decodeHints 0x0⟩,
  ⟨0x22882288,⟨3,by decide⟩,0x22802000,[ew49,ew50,ew52],3,decodeHints 0x0⟩,
  ⟨0x82828282,⟨1,by decide⟩,0x82808000,[ew68,ew69,ew70],3,decodeHints 0x0⟩,
  ⟨0x88882222,⟨1,by decide⟩,0x88802000,[ew67,ew71,ew72],3,decodeHints 0x0⟩,
  ⟨0xa0a00a0a,⟨1,by decide⟩,0xa0800800,[ew66,ew74,ew75],3,decodeHints 0x0⟩,
  ⟨0xaaaa00000000,⟨33,by decide⟩,0xa88000000000,[ew100,ew104,ew107],3,decodeHints 0x0⟩,
  ⟨0xffff,⟨0,by decide⟩,0xe800,[ew3,ew6,ew8,ew9],4,decodeHints 0xf40400014008160541400431064ce0710f3b4ce⟩,
  ⟨0xffff00,⟨8,by decide⟩,0x80e800,[ew22,ew28,ew33,ew34],6,localHints 3 0x98c1a010000081605414 0xf60688d60688⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xaa80a800,[ew73,ew76,ew78,ew79],5,decodeHints 0x990000080000419070190144b11d390801907019⟩,
  ⟨0xaaaa0000aaaa,⟨1,by decide⟩,0xa8800000a800,[ew103,ew106,ew109,ew110],4,decodeHints 0x9940000800004190701900c380d95f0041907019⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe000800,[ew41,ew44,ew46,ew47],4,decodeHints 0x0⟩,
  ⟨0xff00ff0,⟨4,by decide⟩,0xe800800,[ew43,ew45,ew46,ew48],6,decodeHints 0x0⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x33333333,⟨0,by decide⟩,0x32002000,[ew51,ew54,ew56,ew57],4,decodeHints 0x0⟩,
  ⟨0x33cc33cc,⟨2,by decide⟩,0x32802000,[ew53,ew55,ew56,ew58],6,decodeHints 0x0⟩,
  ⟨0x55555555,⟨0,by decide⟩,0x54004000,[ew59,ew61,ew63,ew64],4,decodeHints 0x0⟩,
  ⟨0x55aa55aa,⟨1,by decide⟩,0x54804000,[ew60,ew62,ew63,ew65],6,decodeHints 0x0⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xcc80c800,[ew73,ew83,ew84,ew85],5,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xf080e000,[ew76,ew83,ew89,ew90],5,decodeHints 0x0⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xfe00e800,[ew78,ew84,ew89,ew93],6,decodeHints 0x0⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew79,ew85,ew90,ew93],5,decodeHints 0x0⟩,
  ⟨0xff0000ff00,⟨8,by decide⟩,0x800000e800,[ew96,ew97,ew98,ew99],6,decodeHints 0x0⟩,
  ⟨0xaaaa00005555,⟨0,by decide⟩,0xa88000004000,[ew102,ew105,ew108,ew110],6,decodeHints 0x0⟩,
  ⟨0xcccc00003333,⟨0,by decide⟩,0xc88000002000,[ew101,ew112,ew113,ew114],6,decodeHints 0x0⟩,
  ⟨0xffff00000000,⟨32,by decide⟩,0xe88000000000,[ew110,ew114,ew116,ew118],6,decodeHints 0x0⟩,
  ⟨0xf000f0f000f00,⟨8,by decide⟩,0x800000e000800,[ew121,ew122,ew123,ew124],6,decodeHints 0x0⟩,
  ⟨0x33003333003300,⟨8,by decide⟩,0x20000032002000,[ew125,ew126,ew127,ew128],6,decodeHints 0x0⟩,
  ⟨0xaa00aa00aa00aa,⟨1,by decide⟩,0xa8008000800000,[ew129,ew130,ew131,ew132],6,decodeHints 0x0⟩,
  ⟨0xcc00cc00cc00cc,⟨2,by decide⟩,0xc8008000800000,[ew129,ew135,ew136,ew137],6,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe0008000800000,[ew130,ew135,ew140,ew141],6,decodeHints 0x0⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xe8000000800000,[ew131,ew136,ew140,ew144],6,decodeHints 0x0⟩,
  ⟨0xff00ff00000000,⟨32,by decide⟩,0xe8008000000000,[ew132,ew137,ew141,ew144],6,decodeHints 0x0⟩,
  ⟨0xa0a0a0a05050505,⟨0,by decide⟩,0xa08080004000000,[ew148,ew150,ew152,ew154],6,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa0808000a000800,[ew149,ew151,ew153,ew154],4,decodeHints 0x0⟩,
  ⟨0x2222222211111111,⟨0,by decide⟩,0x2220200010000000,[ew160,ew162,ew164,ew166],6,decodeHints 0x0⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2220200022002000,[ew161,ew163,ew165,ew166],4,decodeHints 0x0⟩,
  ⟨0x8282828282828282,⟨1,by decide⟩,0x8280808082808000,[ew179,ew180,ew181,ew182],4,decodeHints 0x0⟩,
  ⟨0x8888222288882222,⟨1,by decide⟩,0x8888200088802000,[ew178,ew183,ew186,ew187],4,decodeHints 0x0⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8888888088808800,[ew179,ew185,ew186,ew188],4,decodeHints 0x0⟩,
  ⟨0xa0a00a0aa0a00a0a,⟨1,by decide⟩,0xa0a00800a0800800,[ew177,ew192,ew195,ew196],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0a0a080a080a000,[ew179,ew194,ew195,ew197],4,decodeHints 0x0⟩,
  ⟨0xaa00aa0055005500,⟨8,by decide⟩,0xaa00a80054004000,[ew184,ew193,ew202,ew204],6,decodeHints 0x0⟩,
  ⟨0xaaaa0000aaaa0000,⟨17,by decide⟩,0xaaa80000aa800000,[ew186,ew195,ew203,ew207],4,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa00000000,⟨33,by decide⟩,0xaaa8a88000000000,[ew188,ew197,ew204,ew207],6,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe80e800,[ew82,ew86,ew91,ew94,ew95],8,decodeHints 0x9980400014008160541400431064ce0710f3b4ce0148112da711da64e562081a5584ce5810f3b4ce⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xe8800000e800,[ew111,ew115,ew117,ew119,ew120],7,decodeHints 0x99c0400014008160541400431064ce0710f3b4ce00c4a0e1350d93657d6300431064ce0710f3b4ce⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe8008000800000,[ew133,ew138,ew142,ew145,ew147],8,decodeHints 0x9a40e0353c02d3b39a680148112da711da64e56200c4a0e1350d93657d630ed446adaa6a5a87c962⟩,
  ⟨0xff00ffff00ff00,⟨8,by decide⟩,0xe80080fe00e800,[ew134,ew139,ew143,ew146,ew147],8,localHints 4 0x9a83f0100000806134481241605414 0xb980721065403210a980721065403210⟩,
  ⟨0xaaaaaaaa55555555,⟨0,by decide⟩,0xaaa8a88054004000,[ew190,ew199,ew205,ew208,ew212],8,decodeHints 0x9b80c02015040ad200ed03c481241520961580ed129354d9636466d9b0ed511aa6a1639ad61580ed⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaa8a880aa80a800,[ew191,ew200,ew206,ew209,ew212],8,decodeHints 0x9bc000080000419070190144b11d39080190701900c380d95f00419070190edab6a5390801907019⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0808000e000800,[ew155,ew156,ew157,ew158,ew159],7,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3220200032002000,[ew167,ew168,ew169,ew170,ew171],7,decodeHints 0x0⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5440400054004000,[ew172,ew173,ew174,ew175,ew176],7,decodeHints 0x0⟩,
  ⟨0xcccccccc33333333,⟨0,by decide⟩,0xccc8c88032002000,[ew189,ew215,ew217,ew219,ew221],8,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8c880cc80c800,[ew191,ew216,ew218,ew220,ew221],8,decodeHints 0x0⟩,
  ⟨0xf0f0f0f00f0f0f0f,⟨0,by decide⟩,0xf0e0e0800e000800,[ew198,ew214,ew225,ew227,ew229],8,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0e0e080f080e000,[ew200,ew216,ew226,ew228,ew229],8,decodeHints 0x0⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfee80000fe800000,[ew209,ew220,ew228,ew232,ew235],8,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfee8e88000000000,[ew212,ew221,ew229,ew233,ew235],8,decodeHints 0x0⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8e880fe80e800,[ew213,ew222,ew230,ew234,ew236,ew237],11,decodeHints 0x9c00400014008160541400431064ce0710f3b4ce0148112da711da64e562081a5584ce5810f3b4ce00c4a0e1350d93657d6300431064ce0710f3b4ce0ed446adaa6a5a87c962081a5584ce5810f3b4ce⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      viewsBlock3[(i-48)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew2,ew5,ew7],localHints 4 0x150580202014010000300a 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew22,ew28,ew33,ew35],decodeHints 0x81a280020003027c00054150200001058278040581600804050140000a⟩,
  ⟨11,4,[ew13,ew22,ew28,ew33,ew34],decodeHints 0x81a280020003027c00054150200001058278040581600804050140000a0f41a7cc1a02c020340003804⟩,
  ⟨11,4,[ew12,ew22,ew28,ew33,ew34],localHints 4 0x6b09f4e858279f405030068020300002804 0x65d526c22b320a900810772165654432321010⟩,
  ⟨11,4,[ew22,ew28,ew33,ew34,ew36],localHints 4 0xc00b069ac0009f054040389e058020200c0340a 0xfd4ee44dc4bb1221a299348870076055430210⟩,
  ⟨11,3,[ew22,ew28,ew32,ew34],decodeHints 0x81a280020003027c00054150200001058278040581600804050140000a⟩,
  ⟨11,4,[ew0,ew22,ew28,ew33,ew34],decodeHints 0x80b28002030304880c0541502002028584840a05816008080280c0340a0681a7d40220c020000001004⟩,
  ⟨11,3,[ew15,ew17,ew23,ew34],localHints 4 0x7e01a7dc307d815180161b014 0x489428722432065004300210⟩,
  ⟨11,4,[ew15,ew17,ew28,ew33,ew34],localHints 4 0xf40557f069210580c0c09e020830500a1b004 0x5be587b8dd5c2ba299281207600540330210⟩,
  ⟨11,3,[ew2,ew5,ew15,ew33],localHints 4 0x4b9800540005802020040f40c1800a 0xbba699568832776544300210⟩,
  ⟨11,4,[ew2,ew15,ew28,ew33,ew34],decodeHints 0x80b3d002031814880c05415020020f458038584ec0202c02000000680a05816008080280c1b00a010040f40a⟩,
  ⟨11,4,[ew15,ew22,ew23,ew33,ew34],localHints 4 0x2812205458068165fc0a0c09f008830306000014 0x5bf53be3dd8cb8aa59832817611541132100⟩,
  ⟨11,4,[ew5,ew15,ew22,ew33,ew34],decodeHints 0x80b28002029814840a05816008080f430034303980202c02010040680c05415020020300a1800a000000f40c⟩,
  ⟨11,5,[ew15,ew22,ew28,ew33,ew34],localHints 5 0xa06c0156bdae160166b40860dfa068307e48302d820080c000601b03d02804 0x761d2d6a5983b4e669aec60dad330c3858c7b1a10a9ce168693991ad0cc243c830904e78c2012046631084135af631cd6898c5a52a39d494a0e7210a23148300820⟩,
  ⟨11,4,[ew11,ew22,ew28,ew33,ew34],localHints 4 0x2813a1609e0581a0c008008000100a 0x36b36565a34319817731011065654343221010⟩,
  ⟨11,4,[ew22,ew28,ew33,ew34,ew37],localHints 4 0x68022800d0c1fb0540a039210200b010140000c 0xffee4554d51cc11ba199513873376335432210⟩
]

def nodesBlock1 : Array Node := #[
  ⟨11,3,[ew22,ew27,ew33,ew34],decodeHints 0x81a280020003027c00054150200001058278040581600804050140000a⟩,
  ⟨11,4,[ew1,ew22,ew28,ew33,ew34],decodeHints 0x201a3d0080000d27c00054150200001058278040100802c04050140000c0c01a008027f0001b00002804⟩,
  ⟨11,3,[ew2,ew7,ew17,ew28],localHints 4 0x12e0540205000031640f40818004 0xaa4699268832776504300210⟩,
  ⟨11,4,[ew2,ew17,ew28,ew33,ew34],decodeHints 0x21843d0080000d4880005415020000f45803858008024f00003400278040100820c04050140000c0100a0f404⟩,
  ⟨11,4,[ew17,ew22,ew23,ew28,ew34],decodeHints 0x3027c000201a3d008054150105827804050140017f01008180040081a28002008001b000008081800205816⟩,
  ⟨11,4,[ew7,ew17,ew22,ew28,ew34],decodeHints 0xd27c000118427804050140000c0f41a02c1a3980002c00028043d00805415020000200418004008020f408⟩,
  ⟨11,5,[ew17,ew22,ew28,ew33,ew34],localHints 5 0x1b33d09f055b26c49e160146b40c615fe0c01a020027f46c035820006020c0a0f404 0xb6af4c60db95b165614ed69d982b4a55de03bc16b2d8a0602b39919404c002006b5908421640848052c6100b5af631cd6858c211415a9273a0a541ce62948310400⟩,
  ⟨11,4,[ew22,ew26,ew28,ew33,ew34],localHints 4 0x2ca027c1a0c00c1612105802020140000a03804 0x6fe63bd33653cc9b5656a32982776544322100⟩,
  ⟨11,4,[ew22,ew28,ew31,ew33,ew34],localHints 4 0x28030068080349f1609e058020380a010140000c 0x6df6ed9dc61ba1160110013983776335432210⟩,
  ⟨11,4,[ew2,ew5,ew22,ew28,ew33],localHints 4 0x1806040003858008080346c0101a18030 0x67677676cc5b6767aa891876760540332210⟩,
  ⟨11,4,[ew2,ew7,ew22,ew28,ew33],localHints 4 0x164610020385802c830000c010301801a 0x5445cc7b5454aa4545891807605454330210⟩,
  ⟨11,5,[ew2,ew22,ew28,ew33,ew34],localHints 5 0x1b502cf46d00d488156c5ae1805806a0020c02614087fc6c001830303d03804 0xa72af8bddd65094571695a51d3288a54486a90d082a8a21082f089ce7a9414202a54508794a118c252c06313da27358a52d085a949420e529863314a418c4200820⟩,
  ⟨11,4,[ew10,ew22,ew28,ew33,ew34],localHints 4 0xa00c09f0541a160020200003004 0x46a42982773265654343212165654343212100⟩,
  ⟨11,4,[ew22,ew28,ew33,ew34,ew38],localHints 4 0x68083d00c0352202c0e1620105802010140000a 0xff4e9449d41cb11ba114913883376355432210⟩,
  ⟨11,3,[ew21,ew28,ew33,ew34],decodeHints 0x81a280020003027c00054150200001058278040581600804050140000a⟩,
  ⟨11,4,[ew4,ew22,ew28,ew33,ew34],decodeHints 0x81a280020003027c000000202c000100e278040581600804050140000a1601a02002030008080418004⟩
]

def nodesBlock2 : Array Node := #[
  ⟨11,3,[ew5,ew7,ew22,ew23],localHints 4 0x4b8160113d0f414028021b000 0x996726528827065044030210⟩,
  ⟨11,4,[ew5,ew22,ew23,ew33,ew34],decodeHints 0x986280020f43003430020020100e4840405816008040113c0340427c000000220c000000c0f400050140000a⟩,
  ⟨11,4,[ew7,ew22,ew23,ew28,ew34],decodeHints 0x18627c000f41a02c1a030000100e27804050140000a0113b02c0428002008001b000008080f4020581600804⟩,
  ⟨11,5,[ew22,ew23,ew28,ew33,ew34],localHints 5 0x1b7281b627c3061e040200c0f41a2785820c16009b21b014001af02a031800e60804 0xbb2f50836d95c16781f16b26173d8e749dab5a5298b9d58428e746104a6715ad2d944e70400273850781c002d856b0ab5814029d004a007394c500c022084310020⟩,
  ⟨11,4,[ew20,ew22,ew28,ew33,ew34],localHints 4 0x2ca0488152781406830160020200d0300002804 0x6fe638d3cc5607b06560aa0399876565432210⟩,
  ⟨11,4,[ew22,ew28,ew30,ew33,ew34],localHints 4 0xf4068020c09f0540d0300e27808010140000a 0x4de4bdbdcc1ba1994118713653340330032210⟩,
  ⟨11,4,[ew5,ew7,ew22,ew28,ew33],localHints 4 0x4f5860080d02c8300004028301b01a 0xbb7a43343443992812343407605543430210⟩,
  ⟨11,5,[ew5,ew22,ew28,ew33,ew34],localHints 5 0x1b802ca06d9b403921059b01b03006a0620c0861c020f40d002051800460c0a 0x8722f8bddd641d0739ccf31dce7a946420ca5550813853a4e6e908e21222054408409420180278846102003bda77358a52d085a949420e729cc5208430006210400⟩,
  ⟨11,4,[ew19,ew22,ew28,ew33,ew34],localHints 4 0xf40349f05416028300685802c080080003004 0x47e42dc2bb429679aa94212978765433212100⟩,
  ⟨11,4,[ew22,ew25,ew28,ew33,ew34],localHints 4 0x280150301a0c00b020000389e058020100a 0x2ad2b9abccb2a9a98272661541332101100110⟩,
  ⟨11,5,[ew7,ew22,ew28,ew33,ew34],localHints 5 0x1b80349f6ddb50389e6cc1420c300683d02c028206c03187002071800a61404 0xc6316f5b1ad2b4b7c5eedb15852aca779ceb396a503413a4e6d9018002c027884b10220116003c005288e263dcc6b58c5316a49ce829507398a5208430006210400⟩,
  ⟨11,6,[ew22,ew28,ew33,ew34],localHints 5 0x8380b2820d0349f0c0158320b0381a2783d1608305802828081b01418004002090300a 0x72aaadea1066ab972a0a70e03c5eb53de1670ea338d14605543850898d4371204945ad2c60f711a42914b6010b2814a4910428066390262906310020⟩,
  ⟨12,4,[ew68,ew73,ew76,ew78,ew79],localHints 4 0x200701901d65014064400102c0203400 0xcc647672bb947670aa49028767654543210⟩,
  ⟨12,4,[ew73,ew76,ew77,ew78,ew79],localHints 4 0x801211d3e0084b01406004070000b03565 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨12,4,[ew14,ew73,ew76,ew78,ew79],localHints 4 0x2011c1c0481901c050180102c0203400 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨12,4,[ew50,ew73,ew76,ew78,ew79],localHints 4 0x13f11d3e6e44b0640d39806014070040202c00 0x3e63dd52c3b3aa569387212656543212100⟩
]

def nodesBlock3 : Array Node := #[
  ⟨12,4,[ew72,ew73,ew76,ew78,ew79],localHints 4 0x20070065981901c054440102c0203400 0xcca42a32bb740a988470230665454323210⟩,
  ⟨12,4,[ew73,ew76,ew78,ew79,ew80],localHints 4 0x193f04847070000140d5980101ce602c02 0xd734434cb40110aa7099348876543432010⟩,
  ⟨12,4,[ew16,ew73,ew76,ew78,ew79],localHints 4 0x200704b064120140601c0102c0203400 0xcc647672b24aa7099480210767654321010⟩,
  ⟨12,4,[ew40,ew73,ew76,ew78,ew79],localHints 4 0x14011c1c12e1083c073980b01805004020000d 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨12,4,[ew73,ew75,ew76,ew78,ew79],localHints 4 0x2059c1c0151202c060640101c0203400 0xcc6426baa34998484720610554302100110⟩,
  ⟨12,4,[ew73,ew76,ew78,ew79,ew81],localHints 4 0x19400480259c0d12c050640101ce602c00 0xd643344cb4aa61934340880776055430210⟩,
  ⟨12,4,[ew2,ew73,ew76,ew78,ew79],localHints 4 0x2011e1212e1104806014010080b0000d 0xc75bb53a337995181171321654432321010⟩,
  ⟨12,4,[ew18,ew73,ew76,ew78,ew79],localHints 4 0x801c0181901c050480102c0203400 0xb942932aa74091088470230665432321010⟩,
  ⟨12,5,[ew73,ew76,ew78,ew79],localHints 5 0x87a1d080121816711e1c86e1a8641c6ed6612e180161701a1685419005ba01d658500d02e1300800 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨47,5,[ew82,ew86,ew91,ew92,ew94,ew95],localHints 5 0x80470700b120062b407000151340503cd2004100100e058020200c0340a 0xbde49649924c130b5984ad6092528464d924c5307bc22738646358b4a92839cc02948300820⟩,
  ⟨47,6,[ew73,ew82,ew86,ew90,ew91,ew94,ew95],decodeHints 0x802001801008065041c070070040501450004500040b008481200f018012b40101c15054080080c3d44e0304d1340603c013480104016058020200a4bc340280a031031d4061f00600407004072b80218c021d4f587c750000001004⟩,
  ⟨47,7,[ew73,ew82,ew86,ew91,ew94,ew95],localHints 6 0x20048476f41c6f0482b4150c84d03cd26241005839021881f0051d406370610056a5a4075046302cf52b802030000d04e5a0ab02804 0x4d152a4e95aa0e95140d15913485a860b52834b5969c85084cb3a64c846694838e94b4511075961215241215961075144d34514c73a340745141038e12166210722210765912120814159615a7e015a5961417df4d34514c171e74145175d71c15a21b14165b14120815a6591411411441c71451452955966175146175962955144cf4514d238e4d245140f38e2892cb34c20834c2cb2892081451460c21c61451000c2040⟩,
  ⟨47,5,[ew82,ew86,ew88,ew91,ew94,ew95],localHints 5 0x20124800180212c1901c150344d01431004100200b0280e010140000c 0xb5a695d573a51e95cd737a5e9948c78c5618412f738e10b5a15b1635292819cc31948310820⟩,
  ⟨47,6,[ew76,ew82,ew85,ew86,ew91,ew94,ew95],decodeHints 0x802001801124490ac062008001c010000648c190640101c1505408000050143e0043e004ae020630200d0004d13406010310c4010400402104050140000c0112f0d0041d4061f00601c0101c01008023d400138001d4ae8807502804⟩,
  ⟨47,7,[ew76,ew82,ew86,ew91,ew94,ew95],localHints 6 0x20048492004b6fc196f8150d44d03c3162c10050390318a1f0051d4063746101d6c4c001020023d5231380d2b8000d0630296b2ac04 0x4ce52a4e95aa0a951408e58e10d59612152812159610d5144d34674cd3a740d45141038e2865a66085262885969465064c83a44c64648c638e8c845128636211986229934d10684614059615a7e015a5961407c04d339e4c071e74038e75d71c14014014434d14514515a19b14065b14018615a6591d55966175146175961d55144cf4514d238e4d245140f38e14514c08134c1cb2082891862892081c7186145103081000⟩,
  ⟨47,5,[ew82,ew86,ew87,ew91,ew94,ew95],localHints 5 0x208490700603c081201901c0b0300d204050c401040160080e010140000a 0xbde6855945ad5e8551533a0e8915c5545418410f095c10b5815ad434a507318a31908310820⟩
]

def nodesBlock4 : Array Node := #[
  ⟨47,6,[ew79,ew82,ew83,ew86,ew91,ew94,ew95],decodeHints 0x2088203c01124490ac020701c01c011204803c000641900407000024907503c7c03c1000410004080080c0000403d050c431004100581600804050140000a0112f0d0040140504801048012b80218c023d400138002b8758847503804⟩,
  ⟨47,7,[ew79,ew82,ew86,ew91,ew94,ew95],localHints 6 0x20849071c21202b065c101c157003163010058080500c0280f014de18412004ae5086302c023d5241380d1d4000d07c039312ac04 0x5115a95125290925960910913cc92810d5a83cd92410c58c50d86750c46798c86198d4512865a51089252885961069065084635068638864518888612866a03d832029869a7c630614014014459614514551445e50071e74045175d71c14031b15769b15730c1406801571991406191401861576171451550815955014925134515134920814511d034d3ce30c3ce34d1c730c1cb2082891862892081c7186145103081000⟩,
  ⟨47,7,[ew82,ew83,ew86,ew91,ew94,ew95],localHints 6 0x2004849070480658e01c7c1d4061856e4c0080316d2ad8d204057000f37c31005c304016008630d4140004e0c80a4bd050d00e2b804 0x4d182a4e95aa6a982069159130d59630b82830b59630d80d4d38e74cd46778d8e379e4512095962078262075962098094d34654c98e59094519248e320920920c34d2082080615966228206225960618204dd3cf4df4514df3cf79d45120821c69934d20831b6992491005976025171025965405004c24524c03d24004514023cf10034e3062ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨47,7,[ew82,ew85,ew86,ew91,ew94,ew95],localHints 6 0x2004849071c50658f01c15014610f8ae18c0b035322ac4d0187c0ace00c4017101050c16009bf020140004e0300a4bd040d00e1d404 0x5125ea52952a6a95d76926923cd56859c5e83dc55558d5cd51c8e750d4a798d8e399c4922092092165d72082085144a55098e59094929248e32092e22073622072cb2093492082216995e15197df5204925207df69949205e71c3dd34d3dd71c04134d20859b6992491005d85825581025d758054050249350041344049244241010034e3c62ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨47,7,[ew82,ew86,ew90,ew91,ew94,ew95],localHints 6 0x200481c640051845002d332ac48065c701c153d44e0344d0187c03ce10c401718100580218c084bc34038754941440c04001bd0300a 0x5125ea52952a8a95d789289234e34e3565d734d34d51476850e4a89ce75d9e749234d3668a15e65219245254925259248a149234d5a38a138e1c35605995e01d95555835c351949f50375f78349279975d1c331c34139c1c130c3433831c36832196d91d96992032031445d85895581495d758454450949350441344449244941014438f34030f14038e3443041442842092c91492892042041400c61c40461440c3080040⟩,
  ⟨47,8,[ew82,ew86,ew91,ew94,ew95],localHints 6 0x20048ab11e270713002c4b898060656903407056251f0810162403c610c4017200e040630580288c08138140d004002220300a 0x4907a84a75689a779e99055030a5655e17a532155590a78a4a16a348a42388a69a8a14101c35605db7a01db5557c378349b41d48369d70341071b69a1c32193012991c12086032831445565ce4d614e5555044c448e4114843513c44103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨49,8,[ew133,ew138,ew142,ew145,ew147],localHints 6 0xed260d80911cf607c1b0e01312c3a078e6360591304a00c2320405188334ec0b1c46e4f00e0342f1c06d 0x80c7a181b3e181b79e80c3cc7083df71a79f71a3cf70878871a31d7086dd70830c71a6da4c33d94d56194d53cf4c36034d53174c35974c330c4d55954d12144c34944c32084d14910843d008a39008a3cf08438408a30d0842cd08430c08a2ca0862090841c90842080861c60800c50840450840c3080040⟩,
  ⟨50,8,[ew134,ew139,ew143,ew146,ew147],localHints 6 0x7d6f8ac1b8a8490d42b07a2939c480c8150cc3f8a0614184d0e4062c80f058023b80805004001340300a 0x40c80c42149242181f40c48c4085c841e49241e5dd4084882c869c2db31c2db69a2c83084034834195d74194984035c32c32962d53162d528a2c33031c31941c12141c11861c32034044844133cf4134914043c42c430e2cd28e2cd30c2c42841c42091c01891c02081c41840800c50840450840c3080040⟩,
  ⟨51,8,[ew190,ew199,ew205,ew208,ew212],localHints 5 0x1444dd910dd702081f4d8e21248006c3e4d44a49c4803cd30acad04113078500540c020ef0d432 0x637be6621e663bd63610d26dcd6e1cd6ed6d2609625b964b19649ad6270910e1714ed714e1010ec360d75605b56056b60da314d3410e5410d2914e524121141df141e10411e4611ae6016e601ad6116441d2a410ca4112941cc610065110251106310020⟩,
  ⟨52,6,[ew179,ew201,ew206,ew209,ew212],localHints 5 0xec1f1bc370fc203c09c19c19130120d8033a00911c0506c064f9106e4018b02a4e8a702c00 0x7b1dd7f21d7f1ce7b20c1184616a1b1685911a0611958149981494a11986782107d9f77da10782a0a818cacd4aacd8ca814014cd410254100c614e52786117add17ae10785c122d8d2054d2058c22d4a10509108c610907104c62148310400⟩,
  ⟨52,7,[ew179,ew191,ew200,ew206,ew209,ew212],localHints 6 0xec1f1bc370fc20048f72901c164f0270130644c01dc91ac032cc0936405060064400102c021002a0348b0bc00 0x3cc3a33e24233e238e3cc40c0880880a04210a009f08840808829e09d31e09d28a0883083c64103db39c3db4103c638610630c11928a11930c1062860994da08621a0864d30992083c04103d75983d74103c058014030c15428a15430c1402800942150804d50802080944d31001001041861041523cf4103d138e3d14103cf38e10b30c10428a10d30c10b28a081249082208082249081208104107081186105103081000⟩,
  ⟨52,7,[ew191,ew200,ew201,ew206,ew209,ew212],localHints 6 0x3b07c6f0dc3f0806b0d0d9060120d80911c8a06d3e0083800caf04c4b19c0507806004071f42f0000b0342a101c9 0x40c62442346442361840c44c1c91c91e14621e11e01c94491c929f1da31f1da28a1c930941045141e41e41e45141035d35b30c35c28a34d30c35b28a1c62491c769a1c72491c669a40445941561941545140460459531708429758430c09528a1c42141c72491c72081c42490410531c419340345240b3d240b4514033c334b30e04328e34330c04b28a1c32491c72081c72491c32080820851c3185082104043043082040⟩,
  ⟨52,7,[ew149,ew191,ew200,ew206,ew209,ew212],localHints 6 0xec6f0dc3f080123dca42281c1643804c4b078064e86b024b400cd907c180140101c671000b0082a2102f03400 0x40b46340d3e340d45140b3cb0ca0ca0e13e20e10e00ca3ca0ca51f0de2df0de5140ca2ca4053cf41c45d41c3cf4054456c52cb1195146d92cb1055050d925a0c529a0c52490d928a4013d84155d84153cf4015c11d52d61c15161c12cb1d55140c128a0c32490c328a0c12491041d31c11c11041454104514123cf4124514103cf1cc34d1c72cb1ce34d1cc2cb0c228a0c32490c328a0c22491c81c60c21451041000c2040⟩,
  ⟨52,7,[ew161,ew191,ew200,ew206,ew209,ew212],localHints 6 0x3b07c6f0dc3f080120d80911c1b4f8f0270060644c1013a1ac132d4033643a0600501c0102c0219c2a034850bc00 0x3ca7243e33a43e371c3ca38a0880880a13a20a10a008838808859f09e29f09e5960882883c739d3da71d3da38e3c770711a29b10759b10728a11a5960872590822080822490872083c038e3d74183d738e3c040014028a4d459615428a4c05800942150802550802080942491044d21041c71001003cf4103d138e3d14103cf38e10b30c10428a10d30c10b28a0812490822080822490812081041060811c6105103081000⟩,
  ⟨52,6,[ew186,ew200,ew206,ew210,ew212],localHints 5 0x381bc370fc190d81b07867070070ec093a4038b40012d3f4441a2a00111c0b0141807c02 0x7b1dc7d5fc7d5ce7b28c398e63e9db3e8f9399c63c99839ab8399863cab2781d77da177d9ce78200a02a0a118ca12a4a018c39253380d338252390c678e11785d17861078dc31344b38d8b38d2a39cc639d2838cc61048510c0510c8310400⟩,
  ⟨52,7,[ew186,ew191,ew200,ew206,ew209,ew212],localHints 6 0x2346f0dc3f080120d81b0e81c0e0137281901c1e1ac092d80301805444010a88a02c02100180348c0bc00 0x3cd4213d93a13d94103cd38e08a08a09f3a009f09e08a38a08a35d09c65d09c34d08a64a3c639b3da41b3da38e3c640610664610734d1076471063460874d80862980864d308728a3c03973d25973d238e3c058010010010434d1041550922940804d408028a0924d31401c01521861521c71401803cf4103d138e3d14103cf38e10410c08134c0812cb08228a0822cb08128a1091c71041861081c7104186105103081000⟩
]

def nodesBlock5 : Array Node := #[
  ⟨52,7,[ew191,ew200,ew206,ew209,ew210,ew212],localHints 6 0x6b0d03b0186f0dc3f4fc120d81b0248a0a8473641f0714500cb004c2f00005061ca0047e01ce619c0d02c4013002 0x41045142442442445141016340c66241446241465940c44c0820a120c38c20920921f46021f21e20944920720720938920920920738720920921c31d21c21c20930940045b41a65b41a4514006401406001435c31431431405c02c031654351654330c2c05002031d32002532001c72032494044514013d24014514043c42cb2cd20438d2cb30c0840842cb08a2042492081c72082492041c71410c60840001440c3081000⟩,
  ⟨52,7,[ew103,ew191,ew200,ew206,ew209,ew212],localHints 6 0x8d1bc370fc20048363643a0714504c4b3980b1306b00cb70246701805004072281b1002a008182182f03400 0x40d3e241a46241a3cf40d4510cb0cb0e04610e00df0cb44b0cb35e0dd69e0dd34d0cb68b40545c4083dc4084514053c51056856d434d6d46941053450d42990c52d90c528a0d42cb4014514135d84134514015c11041d61c11c110434d0c12cb0c328a0c32cb0c128a1d35151c11451c15141d31454104514123cf4124514103cf1ce1cc0c234c0c22cb0c328a0c32cb0c228a1c62081c71451c92081c61451041000c2040⟩,
  ⟨52,7,[ew165,ew191,ew200,ew206,ew209,ew212],localHints 6 0xec6f0dc3f4fc3606c0911c1f0703812c1901c1e02c401ac132e00301805048010a88a1640219c18034870bc00 0x3cc7233da3a33da71c3cc38c08a08a0a13a20a10a008a38a08a08a08b31f08b08b08a30a3c639e3dd71e3dd38e3c670610631b11369b11330c10668609355908629908655509328a3c03983d44183d438e3c040010449710430c10010009429608055608028a0945551404c04941861544d34801803cf4103d138e3d14103cf38e10410d08130c0812cb08228a0822cb08128a1091c71041861081c7104186105103081000⟩,
  ⟨52,6,[ew191,ew195,ew206,ew211,ew212],localHints 5 0x361bc370fc1c2362e11d40448300e01e00cea04c1b22802064012a40712c0d014180e800 0x729fc731dc731ef7296a3a0e83e9fb3e8f93a1e83a15839998399463a18870db7705f7705ad70de31585538d5538e7439d0839e7238d08701f1741b1741ef701a0581805914a591845814039109380c938108390c610065110251106310020⟩,
  ⟨52,7,[ew191,ew195,ew200,ew206,ew209,ew212],localHints 6 0xec6f0dc3f080120d80972c1c1ac054480b0bc38078032e41307c06064012380706c2a0084019c0d06000 0x3cc6a13cd4213cd69a3cc41024a24a25f42025f25e24a40a24a31d25c35d25c30c24a34a3c541b3c769b3c74103c568504504504130c04119924721824529824520824728a3cf38e3d74103d738e3cf41004105625331625355524928a24955525328a0460542531453c04123d13923d14103c038004034004230c04234204030024228b24020b24028a2422081801c01821451821c21801400400400421020420c2040040⟩,
  ⟨52,7,[ew191,ew200,ew206,ew209,ew211,ew212],localHints 6 0x6b0d08d0186f0dc3f50012518090bc0272c38078032c41319c4012cd9014180e8190047f01ce62280d02c2a16400 0x4d35144e44e44e45144d31634cd6a24cb5224cb69a4cd50d0820a120d64d20920921f52021f21e20950920920920764720720720964920920921c35d21c21c2093494c35144c169b4c15144c368330c31820365830c34d08308330c0972031c72082492081c72032494c05164d54964d55144c048014044014440414444414040030034f3842cf38434d3002c020424a2001ca2002492041c70800c01440461440c3080040⟩,
  ⟨52,7,[ew106,ew191,ew200,ew206,ew209,ew212],localHints 6 0x3b1bc370fc200494611c3804cd907c193980d1646b00cba0248a0180501c01060880bc0b0084019c1e0a800 0x40d3e24174624173cf40d45120a20a22046122021f20a44a20a35e21d5de21d34d20a5ca4064514133dc4134514063c624905b04604624934d2062cb20828a2082cb20628a40045a40265a4024514006402405c061434d6145d42403402142962002d620028a2142cb0401800544d50541860404c04104514123cf4124514103cf04e04c20734c2072cb20828a2082cb20728a249245207185044082041000043082041000⟩,
  ⟨52,7,[ew153,ew191,ew200,ew206,ew209,ew212],localHints 6 0x2346f0dc3f5003611c1c0e01e04c4b0e81901c1b0342a1ac092ec0301805048012280b2242f0084019c4c06000 0x3cc4233d73a33d74103cc38c1ca1ca1e13a21e11e01ca38a1ca1ca1cb31f1cb1cb1ca30a3c539e3d441e3d438e3c540504149d04130c0450451d455c1c529c1c55551d428a3c039b3da65b3da38e3c06400403180535d805330c0405c01d32961c05561c028a1d35554805002531452535134801403cf4103d138e3d14103cf38e04104d1c630c1c62cb1c728a1c72cb1c628a0490481c6145044082041000043082041000⟩,
  ⟨52,8,[ew191,ew200,ew206,ew209,ew212],localHints 6 0xec1f1bc370fc200483606c098ea3911e388dc1c0e01e00c6b04e368d44b8d0058cc06064010bc078ca318c00d02e2f00800 0x50e7a752656752679e50e54e24a24a26456526426324a54a24a3222613a226130c24a38a50156051f7a051f55550178174139b70331b68338e64130124321824129824120824328a5005575164d75165555004c04803904443103c438e34030024428b24020b24028a2442081c00c01840411440c3080040⟩,
  ⟨62,9,[ew142,ew191,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0x3b07c6f0dc3f080f7290490d41c524fd120150c9273f0231340f0f8160e4087351504c7924011048220008f011cc5211400c0951c76014990186401c010900b2f0510081d1c05c030171b441028725c4f63c44f 0x1e5cd423b04dc23304d1a1e5cd971e4889222fcdc022fc8be1e48d922248abd228cbbd228ca952248b921e34d9b28ecd3c28ecd9b1e34d0d2834b9728e4aba28e4b972834a8d22448b82234a0d22449121e24d9b14d93b714d8d9b1e253891424b9714ccab514ccb971424a95222c91222251892224912222d1a314cd53414246b4142552a14cc68d1e14d9b0cc58320cc4d9b1e158050c14b970cad72f0cacb970c1572e221c91222156852214912221d6ad0cac6ac0c1552c0c1468d0cad52a0c143050c284890c183061e80d9b3aa53a73aa0d9b1e813a70694b973298a953298b970694a95229091222451a3224491222911a32850080288868d2888a22285068d0c183211e804a10c1851f1e8029f1e38d9b3a78d1a3a70d9b1e38d1a0258b973260a953260b970258a952244a131e3891222448901e3868d142858b1430489143058b14284890c183870c202850c203870c1828502100840204000020c0820204000⟩,
  ⟨62,7,[ew147,ew213,ew222,ew230,ew231,ew234,ew236],localHints 6 0x80121cc1111c1c1740b65848018ad01c3c000150c84d03cd2040040b595058390200e0343b07c0538c3f0063b650d40843606c09009931c013031921b40308c0a 0x469cf2533ca9a51511b54531a69ad452da69c114539e74d14709e7254beca6fb14509a49b27b8946e2679ec45126d26caecb2db09ac9154517a6a5d4505a695d14459e81514579e71669577655dc5c57458d99052641596632490145188626145008616114407e00114587df01d79871e61d6007006896c065b00925a6590170181456175c014009558a5162952825144ce48245140e3c234208e08e34d28b30224c08b08a249187202142087086145043102002083081000⟩,
  ⟨62,8,[ew213,ew222,ew230,ew231,ew234,ew236,ew237],localHints 6 0x3b07dcf1bc377383f080128f197274215282e19c610443606c0911c1c0880b2f5493f413120062b40707400054eb0c9273f003350231340503cd2004e30400405c16008390200e034910300a 0x4d0a3cbfb53cbfba284d05104cde8d338539cb8df64cd50dbcd7b5334435bf479e30d40d4f0514cb1cf1cb15144f0b708e5410bee79e8e34108e579e32b34db6c71cb6c34d32b71c4c752a8e9a2a8e95144c7a078c74278e47a78e44108c77873247268c73668c771c32434d8c79478e48e48e49648c78c74c15146218226215144c180160141060379f60341060179e30334d60171d60134d30371c6016da08325a0830830812416171596011d96011456171c74c05140954960955144c04800804100843d10844100803cf30434d0802ce08034d3042cb08024a08408a0842440800800861c80801480801c70861450800c00840410840c3080040⟩,
  ⟨62,8,[ew147,ew191,ew213,ew222,ew228,ew230,ew234,ew236],localHints 6 0x200481c014500900b120ad054320f04d03cd2040160e4080b4734a02501c5d3b1078f5cf5c874000cf3e0040ec1f018be0fc010d81b02402145931c00c6486d08c0a2840314813 0x413e37538dd34d051031f3234d37df7ce876310d8c86139041f7f52d3d73d34490412d34cd041f8f22cc308af1b93c6eaeb2134c9410221c0841026186e9af20cbc89a6b8c308b48257249b492172044ec9ebb274d312bac6410129a844101a9a67328126a0430c9e69849441981869461181046045c82186188d45244d39145234d38904128614904228617ce3a030c80e39f30c69b69b79e6dd71a6da61864121961758111609454d4d53543424c248344241034e3c230f08e08d30c0830802c00030022c20092822020890802081461c2102086085104003002042083080040⟩,
  ⟨62,9,[ew191,ew213,ew222,ew228,ew230,ew234,ew236,ew237],localHints 7 0xed981bc377383f080120d8090724045005370500900b145493f4482b4150c81d1c1273f0231340f3481005839020171b63f52d1600c130b81f1d806384012f82501c2206c64008723fa3e2642c030001105f2845202804 0x659e452e60dc52e61e3c0658d9b06522142708dc33b0a0c00650d942e50b3f26f8c3f2ef8b162650c140634dbd1c3de3d1c3cd9b0635e0d1c3470d1c5cb161c3870e263c8bb1c34a3b1c34891263ca1406ccd1a3ae8d9b3ae4d1a06ccd9b1c3873806ccb3826d5b361224a1412ddb3626d4a141c38bb406cc68d061cd9b08c4d3208c4d9b061cd07081d33008b4b3008b5326081cb1626aca14081c8af081ca1426ac89108b50ae081c6ae081d0a108b468d081d60708ac22b08ad62b081c2070604d9b0aa542a0aa4d9b06054010a04b270a893270a88b160a05326267ca140a052250a04a14267d2240a886a30a050a30a0468d0a890a10a050010a7c29f0a7d01f0a042810a042810a103870a142850608d9b3a78d1a3a70d9b0608d1a2e5cc182e64b162e64c182e5cb162648a14162c8911654a1426488911c3878f1c4068d1c4078f1c3868d1220488122460c122458a12204880a1428606083860a142000608080⟩,
  ⟨62,9,[ew145,ew191,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0x4606f0dc3f0803606c490ac1c524fd120ad0543249cfc08c4d03cd2040160e4087411704c2e044071a8ff00092011cc53114024030180509076048bf144013c5291900b0081d1c05e030171b442028725cd262642c 0x2864d992d0cd1a2d0cd9b2864d1a2848b922f04d422f04bc02848d122e5cbbf2e58c992e48b922834d3e3af4dbe20f4d1a2834d8d2035dbc2c38cbc2039dbb2c34c8d2e3923a2e3493a2e352242e389122824d1a14e13b914e0d1a282538914257b714d0cb714d17af1424c992e2c9122e252362e249122e2d22414d153514246b5142552a14d068d2814d1a0cc98b30cc8d1a28158850c14cb00cad7b00cacc990c157af2e1c9122e156ae2e149122e1d6ad0cac6ac0c1552c0c1468d0cad52a0c143050c284890c183062880d1a3aa53a73aa0d1a28813a72c580802c98c992c98b262c58c992e949122e5d2242e5c9122e95224068870e208c68d208c70e068868d0c1832128804a10c1851f288029f284cd9b3a78d1a3a70d9b284cd1a2e5cb98284cc982e5cb15284c912024470e203c68d203c70e020468d142858b1430489143058b14284890c183870c202850c203870c1828502100840204000020c0820204000⟩,
  ⟨62,9,[ew147,ew191,ew213,ew222,ew230,ew234,ew236],localHints 6 0x801211d98070482b4150c84d03cd2040160e4084a0731d006044073b05d02d07300000b43c0103b07c050903f0043606c09009931c00c6486d08c0a00c5108413 0x44f8334724b347282044f48f74b4b18db83175b492c0b80b45b7af44b3ef44b79e45b3cf5884925ab82e5ab4925888204493cf4487ad4483cf44979e5ab92c5882ec5889245ab2cb5c44925e5a6a5e54925c4a694463cf4449e84443cf4469e75e52e65c49265c42cb5e59245c45c45d62085d75d76a14928e28208e24926a182045f3cf45179e4513cf45f79e6996db75c2cb75c6db6992cb5d75d80812185d75950811150834d408c49408c4cc0834920910900833cf08c34e0832ce08334308c2cb08024a083203083243080208085187083103083183085104080080083043083083080040⟩
]

def nodesBlock6 : Array Node := #[
  ⟨62,10,[ew191,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f7506f0dd340fdd3080120d81b02447749d1071493f4482b4700543249cfc08c4d03cd21b41005839021994509d00c131d82e0142c0186100424044071902202c7213c020300005c1d1442102804 0xd5cff6fe67f5fecf30d56550d1f5143b67c6fbeb90d1651e114f74365775f64d34115510c86756f4cf53746590c8cc83485725cb4f234b555c484c840b3afc0846f34838e40b4510c765912d62e12d6590c76071075551284ec1285551074d342a4511073ab10745142a38e12876910722910775d1282080c16591669671666590c194114155515e8e415e5551418e342145114182214145142182015e21f14175f14120815e75d1411411441c71451450c26596dc6186da6590c26182945555d64d35d65552944d340f45128a38e29245140f38e2892cb34c20834c2cb2892081451460c21c61451000c2040⟩,
  ⟨62,9,[ew138,ew200,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0x3b07d7546ce70814f400493c09c12032064150d4e2308231340f140140e40c7591a0247a25011048020740a24dd55391900c13534770149a0185a01c0108871194080980d30453000171b843010725d0d83c84f 0x165d3c23b04dc233053a7165cd97164c6931afcdc01afc6be164cd931a4cabd1a8cbbd1a8ca951a4cb931638d9b1eed3bc1eecd9b163938e1e38b971eccaba1eccb971e38a951a409931a3918e1a389931a411a31624d9b28e0d3928e0d9b1624d092824b9728d8ab728d8b972824a891a346b51a24a091a34993282473428a99b428a870e28259891614d9b0cc58320cc4d9b16158050c14b970cad72f0cacb970c157051a1c9931a156851a149931a1d6ad0c143050c3c70e0c183060cac4ac0c1552c0c144890cad52a167cd9b3aa53a73aa0d9b167d3a70294b973298a953298b970294a951a909931a351a31a349931a911a30c18322167c722285008428844892884a2128504890c187a0167c2851628d9b3a78d1a3a70d9b1628d1a0658b973260a953260b970658a951a34a1216289921e3c8101e4470e1e448101e3c70e1a3468c16284890c183870c202850c203870c182850200080020420402041820200080⟩,
  ⟨62,7,[ew147,ew213,ew222,ew224,ew230,ew234,ew236],localHints 6 0x8012124801cc111740212c0606407054350f00d6704d0ac310400b0282d0399b050390308d0e8053903f0059a1c40902241650d50843807813001371b80308c04 0x46acf2533caaa9151135451eab179450daaa7a8c0d470368a1e45195452faaa8d4525aaaba8a134514e8a2e45171eb2d36c69e79c34d154ae4aab914505a85911a45a29151464a2814d9d79a75cd3459851651648e49259058c501451b8626d45008406d18007e001145b7df01e01b34d6de78034001c01b69d6dc6c06806056405d90051585d709558e5163953825144ca48245138f40234208f08e34d30a2c224208a08a249187202148087086145043102002083081000⟩,
  ⟨62,8,[ew213,ew222,ew224,ew230,ew234,ew236,ew237],localHints 6 0x8d0e9d81bc3775c3f0801253d0002449202426749d085500b88a1841142022008380781312c0606407054350740d294e23080335423134050ac31004e40400b0200a05c0e05004000950e40c 0x4d0c7cabb53cabbc714d05104cde8d338539b78df64cd50da8d7b5334435ab479e30d40d4c9514972c739725144c9c4994941094a7b094a41094979e30a72f94936f94971c30a34d4eb514b6cbacb6c5144eba2b5d9410aa979e5d74105d979e32671ca2734da2771c32634d0872a396426308228a0872494c35225e18225e15144c38035c341f5d879f5d84105c378331835d5c371d5c334d31871c5c325b5c069b5c02495c36835c36435d85d85d86585c35c34c45140954960955144c44840844100863d10864100843c430634e0842ce08434d3062cb08428408624908628a0842440841c40860880861c60840840810c50840050840c3081000⟩,
  ⟨62,8,[ew147,ew200,ew213,ew220,ew222,ew230,ew234,ew236],localHints 6 0x200484920019054350143e0985d0344d0ac31040140e40c0b4734a80709c020f0da30243761761d0d04240a2343a018c30fc01668710203807813000534dc6e08c042880315009 0x413e37538dd34d051036bdb24f6cabacd4d33a2d4d43536288e41025e2634d379e78b434262d094102e28893739b2ce634d27225e7b1213c6fc30490412c30bd041738eb8d36e38e5cd35e8ed2092444ec9ebb274d312b10642a129a844101a9a446045cd3586189c9a049a81092679a61251066061a51846048d45244d39145234d38628924104a28a141061880136078b2df2497cb2de24965a65a75d69c6d96996175811040945404d50140024c248344241000e3c234208e08034d28b30224c08b08a2490830802000030022021461c2102086085104003002042083080040⟩,
  ⟨62,9,[ew200,ew213,ew220,ew222,ew230,ew234,ew236,ew237],localHints 7 0x2359e1bc3775c3f0801253d00124800e013064150d646464053743e098221c40d14ce2308231342b0c41005039030171ba455451c00c090b83a1dc063800730c27004080081d0785a0004f406442682c11468028a215004 0x458d452e60dc52e60d1a0458d9b04462112708dc33b0a0c00444d912e44b3f26f8c3f2ef8b162644c110440d9b08f0d3d08f0d9b0440d10084133b08d4b3b08d53260840b1626b4a3a08408ba0840a1426b4891042cdb91835c391834d9b042dc0b182c60b185cb16183060c26348b7182ca37182c8912634a14182c8361885ab61884810182da8b04acd1a3ad0d9b3accd1a04acd9b183063204acb3226bd8300e1c8910ec583026bc89108116ad08b881008b96ad08108101830bac04ac58b0400d9b0aa542a0aa4d9b04014000a00b270a893270a88b160a01300267c8a50a012250a00891267d2240a002800a108100a142850a885a30a010a30a0058b0a890a10a010000a7c29f0a7d01f0a002800404d9b3a78d1a3a70d9b0404d1a2e5cc182e64b162e64c182e5cb162648a1412248911254a1426488910a1428f040480f183068d183858b183868d183058b0e183860e1c50a0e1c4880e183860a142030404000⟩,
  ⟨62,9,[ew145,ew200,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0x4606f0dc3f0814f400490ac800e01e04c48064150d4e2308231340f0c41005039031d045c2e01c11009731780a249d554919024030180509877048c414c01088711a8085d10a1680d000171b8420104f3fd262682c 0x2864d992d0cd1a2d0cd9b2864d1a2848b922f04d422f04bc02848d122e5cbbf2e58c992e48b922838d1a1ef4dbe1ef4d1a2838d8e1e39dbc1ecccbc1ecddbb1e38c992e412ba2e3893a2e392a52e409122824d393ae1bb918e0d1a2825b8918257362c28cb6182972e2c24c892e289352e252b52e249122e292a518247341ea59b418a470e1e259892814d1a0cc58320cc4d1a28158050c14caf0ca972f0ca8c990c157052e1c92d2e1562d2e149122e1d62c0c143050c3c70e0c183060ca84ab0c154ab0c144890ca94a9287cd1a3aa0d9b3a9cd1a287cd9b2c580802c98c992c98b262c58c992e912a52e5c9122e5d2a52e909120c18323287c723068850a1884489188450a060c4890c187a0287c285284cd9b3a78d1a3a70d9b284cd1a2e5cb98284cc982e5cb15284c9121e3c8101e4470e1e448101e3c70e023450a182c489182c50a02044890c183870c202850c203870c1828502100840204000020c0820204000⟩,
  ⟨62,9,[ew147,ew200,ew213,ew222,ew230,ew234,ew236],localHints 6 0x80121248012d9e064150d44d03c31040140e40c4a8731d00601c11009073683c034c00b45d0283b07c050983f0059a1c4080e01e04c004dc6e08c0400c5308409 0x44f8334724b347282044f48f58c4925ab8315ab49258c82044d7f044c3f044c7df44d3cf6c84af8d982f6d9492b888084593ed4487ed4483cf4597df6c832c5a4aec6e430c588ac85c44925e5a6a5e54925c4a444463e84449e84443cf4469e75c45c45d630c5d75d75e52265c49265c42085e59246214928e28208e249262182045e7df4513cf4517df45e3cf5d75dd08131d61c6596da2086da6596182085d75950811040834d40804940804c00834920910900833cf08034e08330308334308030c08928b08320b083283089208085187083103083183085104080080083043083083080040⟩,
  ⟨62,10,[ew200,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f7706f0dcee0fddb0801253d00124801c4380781312dda7641905435388c208c4d03c311b81005039031994649d00c091dc2e0142c0186101c2604401020021c85a0740d13c0005c220285308404 0x9563f6fe67f5fe61809565508ef4e43b67c6fbeb908e64ee0e4f74365775f64d340e54e08d65913463513465908d60d10d5551284f312855510d4d343147210d3b210d45143138e0866706efbb02af659086b8628656d5c84ed288555b064c64083aaac646a28638e40845128636911da2929d34d106a0608065916696716665908094014055515e8e415e5551408c04213a214082214038e42182014014014434d14514515e19f14075f14018615e75d0816596dc6186da6590816181d45555d64d35d65551d44d340f4511c738e1d245140f38e14514c08134c1cb2082891862892081c7186145103081000⟩,
  ⟨62,9,[ew133,ew213,ew216,ew222,ew230,ew234,ew236,ew237],localHints 7 0x3b07d7847d06208f7290493c09c04c48141de478091ec970443e0200c258e23084d0e40f0c4160d4140c80a05ddd5511d00c2354c780149b018460400108859198020744c158002a9770bcf313c28038c515404 0x45d9423b04dc23305932045cd97044c21308fcdc008fc23e044cd93084cabd08b8bbd08b8a95084cb930438d9b1eed93c1eecd9b043990e1e38b971e8caba1e8cb971e38a8e0840993083970e0838993084172e0428d9b16e1bb916e0d9b0429b8a1628b971684ab61684b971628a8a08309930829a8a08289930831ab5162858a163c70e162c58b04acd9b3ad19323accd9b04ad9320cc0b9732c4a9532c4b970cc0a9508bc993081172e081099308bd72e162c5ad04ac70e162c7ac04ac50a0400d9b28a4d2a28a4d9b0400d002800b97289d328289cb97280130008102250800a000810993280072428811a4288070e2801180288052228010a2280050a28810a02800f802818a092850f9f2800a000404d9b3a78d1a3a70d9b0404d1a1058b973260a953260b971058a950810a1204049921e3c8101e4470e1e448101e3c70e162c60c163450a163460c162c50a0c143050c184890c184070c1430508102030404000⟩,
  ⟨62,9,[ew133,ew213,ew220,ew222,ew230,ew234,ew236,ew237],localHints 7 0x8d5e11f4197a0d81b124800e0132b450055de478090143e044f31980d258e23084d0e42b0c416020140300a05ddf5551c00c230b83a1ec06114100052b1a00b404020741e158002a9790bc970b027038c615004 0x4599422e60dc22e619320458d9b04502140900dc1090023f0450d940850b3e08c0c3e08c0b160850c140438dbd3af193d24f0d9b043990e243933b2e40b3b24413262e38b0e0840a3a083983a0838a1408418300428db91631c391630d9b0429c0a162858a165cb16162c58b0830a370829b370828a140831b3616291b5168473516851a3162870a04ad9323ad0d9b3acd93204acd9b162c5b104acb3108bd8300810a14081183008bca140cb881024b470e24b48100c1870e162cbac04ac50a0400d9b2aa4d2a2aa4d9b0400d002a00b282a9d3282a9cb162a0130008102250800a800810a142a007242a811a42a8070e2a011802a805222a010a22a0050a2a810a02a00f802a18a892a54f9f2a00a800404d9b3a78d1a3a70d9b0404d1a2e5cc182e64b162e64c182e5cb160810a930404a13103c810244470e2444810103c70e162c60c163450a163460c162c50a0c143050c184890c184070c1430508102030404000⟩,
  ⟨62,9,[ew133,ew213,ew222,ew228,ew230,ew234,ew236,ew237],localHints 7 0x3b5e11f418820d8092003e9211e0141102c960e01e04c482b45005647158e23084d0e40f0c416020170500c029e05591600c230b81f1ec06110100042206c66008aa0bc970b10b17c0d5ecfe00025038c714804 0x459e422e60dc22e61e3c0458d9b04502140900dc1090023f0450d940850b3e08e8c3e08e8b160850c14043cdbd2045e3d2044d9b043de0f203c80f205cb1620408100844a3b083dd3b083ca140845d3a04d18b13ae4d9b3ae18b104d0d9b204083704d0b3708d972e0810a14081172e08d8a142040bb504d078f0414db33ac98b314c8d9b041588514153302e20b3014213262e14b050820a2f081572f0814a14082172e14151ad20807ad14811a3201478514155851821608142158818146050400d9b2aa4d2a2aa4d9b0400d002a00b282a9d3282a9cb162a0130008102250800a800810a142a007a42a7d1a42a7c78f2a011802a011002a30a8e2a551222a00a802a7c2a12a010212a002852a7d01f0404d9b3a78d1a3a70d9b0404d1a2e5cc182e64b162e64c182e5cb160810a930404a132040891204878f2048891204078f182c60b183070e183038d182c60b0e18408142428514244080e1828508102030404000⟩,
  ⟨62,10,[ew133,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f5e11f418820d81b0244778c800f8380781312de22b450055e1388c21343903c31058080500c028ac4789d00c231ec2e0142c01817040011982202c4f008560740d2a872000110389608404 0x95d7d6fc67d5fcd7509565509111113a67b13a1390916511114f81315781314d311155108b6776f6d773f665908bd4b3cb5745cd4f43cd555ccb4cb10d47210bc7210b45110dc710856706efbb02af659085b8528556d5c84ed288555b054c510846b105aab105451108aaa2858293de2e929e820a052c50806594a66274a66590806004805554a48e54a45554808c01041221004801044514802e149d82149d2cb48080049d15f48079f48014549d79d0816596dc6186da6590816181d45555d64d35d65551d44d31044900814501cc34d3ce2cb3ce34d1cc2cb1c62082891452892081c6145104103081000⟩,
  ⟨62,7,[ew147,ew213,ew222,ew223,ew230,ew234,ew236],localHints 6 0x820484907073018110205d1202b0640702c0c0f00d6808103c31040160d42d0399f05032028d7188053943f005461640900a49650d608545130130004a0cc0308c04 0x461d33534ce18515113545278729d450d84d9e8c4d471368a2745171453086f69451c861b9f7d34514df7ee451967b6c34d8e79e534d154524aab914505a85911a45a29151464a2816716434d9279c53451651648e69259058c501489b8626d45008406d18007e001145b7df00d79775e5cd34074001c01b69b6dc6c06805c564061900515761709558e5163953825144ca48245138f40234208f08e34d30a2c224208a08a249187202142087086145043102004083081000⟩,
  ⟨62,8,[ew213,ew222,ew223,ew230,ew234,ew236,ew237],localHints 6 0x35c627946f0dde40fc82048f7290091241c929a12742155c2e018d9184110210c088f0270131202b0640702c0c0740d2984a0cc03358232040503c31004e5040160083505c0e05004000980c80a 0x4d0cbdafc53dafccb24d05104cdecd33953abb9e374cd50dacd3f6335436af53cf30d40d4c9514933cb49335144c9c8990941091b3f191b4109093c931b73090937090971c31b34d4ec514badbedbad5144eca2c087410aea3e90824100873cf3262cba2734da272cb32634d5d96e59232495d76db5d92494c35145e18225e15144c38035c34105d879f5d84105c378331835d5c371d5c334d31871c5c36c35d82495d86db5c32435c36435d85da5d86585c35c34c45160954960955144c44840844110863d10864100843c430634e0842ce08434d3062cb08424a08020a0802490842040841c40860860861c60840840800c50840450840c3080040⟩,
  ⟨62,8,[ew147,ew209,ew213,ew216,ew222,ew230,ew234,ew236],localHints 6 0x20849070480ac1901c730a40803031040160d4140c80a0b405048281750d0f0db3024b7957c1d0d14b00e35c6203cc80fc01518590094513013000571283308c0428c0915403 0x413de35378d34d0510373da94f6a73ccd4cd3b1d4d435371c4e410253d27cf49d34c9cc92d0c89c7225040bc7125e26034d79e797514c134f05145d34efaeb490412aebbd041e7ae20d35e82d2092446045d34d8618190b04aec110406aeb10daa6a6a98d344a44989a049e81092669e61251066061a51846046189014e48a38d24104a38e241080e3a134d84e3a034d78b2df2497cb2de24975a75a65971a6da6596175811040145424d50940804c048344041008e3c034000e00234d28b30024000b00a2490830802000030022021461c0107006005104003002042083080040⟩
]

def nodesBlock7 : Array Node := #[
  ⟨62,9,[ew209,ew213,ew216,ew222,ew230,ew234,ew236,ew237],localHints 7 0xd76886f0dde40fc823dca41241c3c09c04c480ac1901e4e4802e188de0a40803057128230c4100583505032028170ce4d5611d0240303c0537c123202800422164690081d1305b0004f40a4c26c2c11878038a315404 0x464dc408bcd4408bcd9b0464d1a044e1932b04d423b0603f044cd13084ccbe2a597be0858c992a4d793043cd1a20f0dbd20f0d1a043cd8f203dabb2090cbb2091ab5203cc8f2a459ba203c9ba203d9b32a44993042cd1a18e1bb918e0d1a042db8b182ccb61889ab61888c99182da8b2a349b4182d9b4182c9932a359b3182c60b184078f183060c04a8d1a3ac8d9b3ac4d1a04a8d9b08117af08c0c9908c17af0810c992ab5326122499312b93262ab4993183062c04a878f183082b04a858b0400d290a7d4290a7cd1a04014000a002800a10c990a142852a7c9a70a013270a009932a7d3260a007a50a852250a8478f0a012000a845a30a011230a0058b0a851210a010000a7c29f0a7d01f0a002800404d9b3a78d1a3a70d9b0404d1a0a142980404c982a50b160e1c9930e5cb162a509932040891204878f2048891204078f183068d183858b183868d183058b0e2838a0e1c3060e243880e1c3060a142030404000⟩,
  ⟨62,9,[ew138,ew209,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0xd75d51b39d7a0d81b1241c3c09c120320ac190544a08cd214016020140300a7591a02405048113c8650740e24de65652000c130b8621e80f16c070052d1a40b408020a40d32457000170cc43010725f4d82502c 0x16593c22e60dc22e613a71658d9b16506941b00dc11b006bf1650d941a50b3e1a94c3e1a94b161a50c141638dbd3af13bd24f0d9b163938e2439abb2e40b3b2441ab52e38b0e1a40a3a1a392ba1a38a141a412a51624d9b2ae0d392ae0d9b1624d092a24b372ad9ab72ad8b162a25a891a346b41a24a891a34a142a256b32aac7332aad6ad2a247091614db20c1d8b20c1cd9b16158850c143050c5cb160c183061a1ca301a157b01a14a141a1d7af0c1472e0ca96ae0ca870e0c156850ca84ac0c155ac0c144890ca95aa167d3a73aa4d9b3aa13a7167cd9b0c18326167cb261a912a51a34a141a352a51a90a14028c810248870e2488810020470e2a540842a844892a84aa12a544890c18ba0167c2851628d9b3a78d1a3a70d9b1628d1a2e5cc182e64b162e64c182e5cb161a34a931628a13063c810244470e2444810063c70e1a3468c16284890c183870c202850c203870c182850200080020420402041820200080⟩,
  ⟨62,9,[ew142,ew209,ew213,ew222,ew230,ew234,ew236,ew237],localHints 7 0xd71bc370fc823dca41243507038078131202b06415128230c43e058080500c029cd4540504811089711700e23de65692000c090b8621e40f1a4070042902cca15c025f50e16c0d000170cc410104f408f62402c 0x2058d422e60dc22e60d1a2058d9b204c9132500dc1250093f204cd93244cb3e2494c3e2494b16244cc132038d9b2af0d3d2af0d9b2038d0e2a39a3b2ae8b3b2ae9a342a38b0e24489392438a8e24489932024db83addb3818dcd9b2025b091824b352e29a351828b162e25a0924289b324252b3242499324292a518256322aa873218a962c2a247092014db10c1d8310c1cd9b20158050c143050c5cb160c18306241c9af241572f2414993241d72e0c1472d0ca562d0ca470e0c156050ca44ab0c1552b0c144890ca5529207cd1a3aa0d9b3a9cd1a207cd9b0c18326207cb2624912a5244899324492a524909932a540842a8c70e2a8caa32a5470e028850a1884489188450a02044890c18ba0207c285203cd9b3a78d1a3a70d9b203cd1a2e5cc182e64b162e64c182e5cb162448a94203c9932448911203c70e063450a182c489182c50a060c4890c183870c202850c203870c182850200080020420402041820200080⟩,
  ⟨62,9,[ew147,ew209,ew213,ew222,ew230,ew234,ew236],localHints 6 0x20849070480ac1901c156883104016020140300a01412044c04345d02d0736c3c034740b473038d71880f0a43f0043606c020e01e04c001283308c040245708403 0x44f4b34624f346249244f4cf7ccbf259d4b27ddbef58c48c45db7144c3f144cb6d45d3cf6c84b0599bf06d9492588bc84593ee448b6e4483cf459b6d6c89ec7e532c6e59e7ac83085c45c45d64925d75d74463ea444a6a4443cf446a695c43285e49e85e430c5c49c45e42265c49665c42085e49645d75e30814a34618a24513cf4518a24613cf62075d7de30c7de75d61830c61c6596da2086da6596182085d75950811040804d40834940834c30804800910900803cf08334e08030e08034008330c08928b08020b080280089208085187080107080180085104080080083043083083080040⟩,
  ⟨62,10,[ew209,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0x35dea1bc372c83f208620d81b125e907038078131202b7a01901c1579c4a08c310cc10058080500c029994809d0240303c05184120a4110044f1a42202c021c85b0740d0b00005c2e0385708404 0x9767d13663d136659097618091f114fa63b6fae780916111115f74d4db71145d74d1d9108c6356f46753f461808c64c3ccb3310d5f33cdb2c10c5cc4cda71c8c4713cca694cd4510866306efbb02af618086b862865ed108b2d2885d7106b064c846aac6a6a2864514c8a692868283de32829e8209c63060806261639661636180809401401401445d71451454e34641408a41404514e38a214032115d82115d30c14080015d19f14079f14018615d79d0816596dc6186da6590816181451560815d64d25141c74511d55144d24511d034d3ce30c3ce34d1c730c1cb2082891862892081c7186145103081000⟩,
  ⟨62,9,[ew145,ew213,ew216,ew222,ew230,ew234,ew236,ew237],localHints 7 0x4606f0dc3f080f7290490ac1c3c09c04c4806407941170b8110200c2484a0cc231340f0c410058350503202a4f109dd56d1d02403018050a078048cb15401088591a8020744c1780013cff4982c5dcf91180e26c04 0x2864d992d0cd1a2d0cd9b2864d1a2848b922f04d422f04bc02848d122e5cbbf2e58c992e48b922838d1a1ef4dbe1ef4d1a2838d8e1e39dbc1e90cbc1e91dbb1e38c8e2e41a3a2e3893a2e39a342e409122828d1a16e1bb916e0d1a2829b8a16294361688cb616894281628c8a2e309352e29a352e289122e31a34162858a163c70e162c58b28b4d1a3accd9b3ac8d1a28b4d9b2c580862cc4c992cc4b312c58c992ec13262e5c9122e5d3262ec0912162c5af28b470e162c7ae28b450a2800d2c3aad52c08acd1a28015000800ca92c094290808c992c014002e089272e013272e009122e0932608007251e85225088470e1e0120008845231601123080050a16851210800f8010090020808f821000400284cd9b3a78d1a3a70d9b284cd1a2e5cb98284cc982e5cb15284c9121e3c8101e4470e1e448101e3c70e162c60c163450a163460c162c50a02240890204306022008702043060214102080c000080c1020204000⟩,
  ⟨62,9,[ew147,ew213,ew216,ew222,ew230,ew234,ew236],localHints 6 0x80121241c1201901c731d006044080312c205a203c3104016174350503c0c80a68cd10b40e3003b07c050a03f00546164025144c04c00084091283300c5508c04 0x44fab34724b3472aaa44f48f7cc4927deab17de4927cca8c44db7044c3f044cb6d44d3cf70849271baaf71b492708a8844a3ee448b6e4483cf44ab6d70870871f30c71c71c56b4929acaaa9ac49256baaa4698614513cf4518614693cf71c72808730c71c7e70872086004a59968e56164929008c04563e24408624403cf4568616003207da7a061a30c7c078061a21d7006dd60020871a6da6005c05566566165d65405400834d40864940864c60834920910900833cf08634e08330308334308630c08928b0832030832830892080860860831c30830830861c6081105083005083103081000⟩,
  ⟨62,10,[ew213,ew216,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f7b46f0dcee0fdec080123dca41241c164f02701312019130077ac9d0242e0b006184110200c0851d1283300c5508c782040579c0f784310042804016008220d4140001d0c80a2a84605c0e13c04 0x6969ff7be6ff63e9e76966d6691f5143b6fc7bbeb96916d1e119374365b763692441159168d6db3349f53346db68d9cd30d59630b93330b59630d90d431ab230d47230daaa4314516896db22fbb022f6db689b8920959620792d20759620990942b46c209aac20945142baaa20920920c34d20820869f6db7a99e77a86db69f9e70655966269246265960659244223cf0414510633cf42245120822169f34d20832069f2496806dd79c65d11c6db6806401005976025171025965405004024524c03d21004514023cf10034e3062ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨62,9,[ew138,ew213,ew222,ew228,ew230,ew234,ew236,ew237],localHints 7 0x3b5d51b39c200d809070129491a0141102c933c09c12032064150744a0cc231340f3485005808944430500c029e05711600c130b81f1e80617c070042206c6500872360940b025034cc148005ecfa1100e3f804 0x1059e422e60dc22e61e3c1058d9b10505141500dc1150053f1050d941450b3e14e8c3e14e8b161450c14103cdbd2045e3d2044d9b103de0f203c80f205cb1620408101444a3b143dd3b143ca141445d3a10d0d1a3ae4d9b3ae0d1a10d0d9b204083710d0b3714d93261428a14142932614d8a142040bb510d078f1018d9b2ac8d332ac8d9b1018d062a194312ac0b312ac14282a18b06142852f1418a861428a142a1922e2a807ae2a812242a187862a196862a30a8e2a556ad2a18a861000dac3aad52c08acd9b10015000800b292e094290808b162e014001408a2714013271400a14140932608007a5207d225087c78f20012000801100180918208091021800600087c3212a0102108003062a7d01f101cd9b3a78d1a3a70d9b101cd1a2e5cc182e64b162e64c182e5cb161428a93101ca132040891204878f2048891204078f182c60b183070e183008d182c60b1428509101c3060214102080c000080c1020204000⟩,
  ⟨62,10,[ew138,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f5d51b39c200d81b024477b81c048f0270480c8190544a0cc23205e803cd214016764080500c028ac4689d00c131e82e0142c0181d01c011942202c4f0081103493084002a84305c0e1c804 0x215d7d6fc67d5fcd752156552112912ba67b2ba2b92116512914f82b15782b14d329155120b6776f6d773f665920bd4b3cb5745cd4f43cd555ccb4cb28d47228bc7228b45128dc712066594af6304af6592066064865554ad4ee4ad5554864c628a2ac28648628a45148682b49e2eb49e8204862c620066a6e9a2a129659200a001005675c29671025559809402824642808e42804512828e31002e23dd82211d2cb84080011d19f48079f10018649d79d2076596dc6186da6592076180545555d64d35d65550544d328a49020745004c34d3ce2cb3ce34d04c2cb28a289207186045082103000103082041000⟩,
  ⟨62,9,[ew142,ew213,ew220,ew222,ew230,ew234,ew236,ew237],localHints 7 0x8d1bc370fc203dca4124350703804c190481595115014110880d23c4a0cc231342b0c43e058080500c02a53105df5751c00c090b83a1e4061a0070042702ccd150020741e1700013cf62402c5e4fb1140e40404 0x2058d422e60dc22e60d1a2058d9b204c9132500dc1250093f204cd93244cb3e24d4c3e24d4b16244cc132038d9b2af0d3d2af0d9b2038d0e2a3943b2ae8b3b2ae94282a38b0e24489392438a8e24489932028db81631bb81630d9b2029b8a162858a165cb16162c58b24309b62429ab624289932431ab5162923416887341689224162870a20b4d1a3accd9b3ac8d1a20b4d9b162c5b120b4b3124c13262448993244932624c09932a543892abc70e2abcaaf2a5470e162cbae20b450a2000dac3aad52c08acd9b20015000800b292e094290808b162e0140024089a724013272400993240932608007252a85225088470e2a0120008845231601123080050a16851210800f800e090020808f820e00380203cd9b3a78d1a3a70d9b203cd1a2e5cc182e64b162e64c182e5cb162448a94203c9932448911203c70e162c60c163450a163460c162c50a0e183860e1c4890e1c0880e183860214102080c000080c1020204000⟩,
  ⟨62,9,[ew147,ew213,ew220,ew222,ew230,ew234,ew236],localHints 6 0x20048490701901c150143e044c01740b0344d1cc2b0c41042416678080503c0300a68cd00b40e1d08d0e80609c3f0043606c020e01e04c00024211283300c5408c04 0x44f4b44734f447349244f4cf84c9329684b286892494c48c468bf144c3f144cbef4683cf70870872549271c71c44a3f0448bf04483cf44abef7087ae71b32e71b79e70830871c72d0864ad46bb2c4513cf451b2c46b3cf56aa2886930c869a2855530c71c9670862086004a69569266164929409004563e34408a34403cf4568a260032085a7a061a30c7c078061a21d7006dd60020871a6da6005c05566566165d65405400834d40874940874c70834830910900833cf08734e08330e08334308730c08928b08320b083283089208083083087187087087083183081105083005083103081000⟩,
  ⟨62,10,[ew213,ew220,ew222,ew230,ew234,ew236,ew237],localHints 6 0x8d7c06f0dcb20fc200483a0d81b125ef0703804c1907807055eb27409014610f81113c2202c0d0851c1283300c5408c4d0182e0ade20c40109c101a016009da020140001d0300a2a84505c0e0b004 0x697a3e5b66fe5b6a286976db692f5247b6fc7bbeb96926d25925f8477db85b75d7452d9268d6f57b4a353f46db68da0d3cd5735a15f33e155558d5cd461b31c8d4b13cdb2c4614926896f022dbf022d6db689bc92092092165d720820846d4ae209b2e20949246db2c2092eb20736b2072cb20934969fa287aa6db7a9a2869f6db20822769f5e74649650414920669654644920638613e234d3e286104134d2085a069f2496806dd79c65d11c6db6806401005d85825581025d758054044249350041310049244241010034e3c62ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨62,10,[ew142,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f1bc370fc203dca412435070380781312def064120544a0cc23205e903c310f816020147440c028ac4549d00c091e42e0142c0182201c010440b23c21008721701d034002a84105c0e13c04 0x35563d6fc67d5fc6183556553503d03fa67b3fa3f93506503d04f83ec5783ec4d33d055034b6594b66374b665934b60b48b5554b44f54b455548b4cb3cf3f33cb48b3cf4103466726f1c32271659346c0624656f5c74ef247555b864c63c742d3c6b2d3c64103c7b2c24686b49e2eb25e8614862c634066a6e9a2a129659340a001005675c29671025559809403c24243c08e43c04103c28e31002e249d86211d2cb48084011d1a02407a01001867dd79d34c6596dc6186da65934c6180545555d64d35d65550544d33cf49134c4103cf3ce34c2cb04a1c72481862481c7041186045082103000103082041000⟩,
  ⟨62,9,[ew147,ew213,ew222,ew228,ew230,ew234,ew236],localHints 6 0x200481c014500440b1201901c1541c3c0344d1cc0f0c4100585d021a30b40e1d0f8050cf6600c0283b07c060943f0043606c09008210e01e04c001283300c5208c04 0x44f4b44734f447349244f4cf80b80b82549282082044daf244b3f244baeb44d3cf82083108a4b146fc304513cf451c3046f3cf82096e08a2cb68692d9674ad6a79249464864673ec446aec4463cf467aeb6867ea8162ea6967df8062c6686a066e7a676a7a276c66c66004a695c92661c49294090045c3e34408a34403cf45c8a26002e18157e16152cb8007c06007406dc79c61c75c6c06c06151996805996001865d55950834d408c49408c4cc0834830910900833cf08c34e0832ce08334308c2cb083083087287087087083283087209083189083203087186081105083005083103081000⟩,
  ⟨62,10,[ew213,ew222,ew228,ew230,ew234,ew236,ew237],localHints 6 0x3b7c46f0dcb20fc200481f0d8090701b9549d014611401102c210e01e04c487b81901c151c81d035161283300c5208c4d0182e03de30c4010941005802088082a8170382c17c1411004001d20300a 0x697d3e5b66fe5b6d346976db692f5247b6fc7bbeb96926d25925f8477db85b75d7452d9268e6f5372d353726db68ed0e34e34e3565d734d34d4728f334e4b334e8e34724926aa9e77b16db7b09e76aa6db34d36f6aa5ef46cb6d20849222eb6d46c49234d5ab6aa38e6836e97a89e91e86db6839c31c356659f5e61df5555835c345f4a49438e41c349245f8e31c33223413a21c130c3433831c380321f85f1df81f2032036846dd79c65d15c6db6846441445d85895581495d758454444949350441314449244941014438f34030f14038e3443041442842092c91492892042041400c61c40461440c3080040⟩
]

def nodesBlock8 : Array Node := #[
  ⟨62,10,[ew145,ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0x1181bc370fc200d81b1242b07038078131201901c157b04a0cc231340f0c410059db0201474c0c028ac45c9d02403018050442e048920840113c6a0880b008721781d034002a84205c0e0b004 0x49765753c61853c65949761849055057a63b57a5794906105555785545d755055048b6376f66773b661848b64b38bd3550c5f538cd3450b5cb54cb7354b43354bb6d54c4104866326f1c32271618486c062469af5075ef2479a65065c654742e546b6e546410547b6d24686c39e2ec25e861ac62c648062a6e9a2a129618480a001005e75029a71025d75009805424255409255404105429241002e339d86311d2cb88084011d1a02407a01001867dd79d4916596dc6186da6594916185555564915d655551349141004f30c38d2cb38d30c0412cb04a1c72481862481c7041186045082103000103082041000⟩,
  ⟨62,10,[ew213,ew222,ew230,ew234,ew236,ew238],localHints 6 0x3b084015bc360244702c3804c4b018e703415128032b02369081014b203c3f045060397e058023b808578144e004001340300a 0x5d38e85dd6285dd8dd5d36139e79e69d06263d075d3e54d33e575d3d04d35e16245ca8e45ca6185e18e130a4e25617623214d348a74a3e17213ca40a3ca70a3e14215db6205c37e05c36185db7db1c34de55b75e1db4d34837433db41b3c37033c34033db71b1c321a30129a1c12082432835cd6195c45995c46185cd58d1444d454d45414d4d34844443cd40d3c43843c44043cd38d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨62,10,[ew147,ew213,ew222,ew230,ew234,ew236],localHints 6 0x20048477c41c02c4b7c0060640d01c157b473205ea03c310381017416770080f0140b5d40300a0ec1f014110fc010d81b024020e01e04c001283300c2108c04 0x40eab2431472431aaa40e44e74a47092dab076d451bcaa8a42d9ee40a3ae40a9e742d38e64646c928aac668451ac6a864283a94069e940638e4289e76466a67552a665569a9462865c046391f8635df45188084041f3a04007a040038e41f79e5c029c75469c5d428a6c06805d41986405585c018659455408349308b45308b48b08345109008f08338e08b30d08328d08330308b28a087209083189083203087186081105083005083103081000⟩,
  ⟨62,11,[ew213,ew222,ew230,ew234,ew236,ew237],localHints 6 0xec1f9846f0de600fe5f080120d81b0244797a5d0700b0e01e04c4b9700696c19034070565a2744a0cc03084230b8810165903e580c4010440e040220580295c080741405c04002560300a 0x655bfb77a6bb5fabef655695650e503f76b8777db5650690d109333f25735f29243d055064a6b1770bf133069a64abca30a56e5ea92e32a555b4a90a3ea82bb0a42b30a8203ea4106436a97689e91e869a6439c31c35665e19261e15559439033e14228c38221c34103e18201c321f30129f1c120878328364469c75b61c15b69a6446041445565ce4d614e5555044c43ce4114843511444103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        nodesBlock0[(i-0)]?
      else
        nodesBlock1[(i-16)]?
    else
      if i < 48 then
        nodesBlock2[(i-32)]?
      else
        nodesBlock3[(i-48)]?
  else
    if i < 96 then
      if i < 80 then
        nodesBlock4[(i-64)]?
      else
        nodesBlock5[(i-80)]?
    else
      if i < 112 then
        nodesBlock6[(i-96)]?
      else
        if i < 128 then
          nodesBlock7[(i-112)]?
        else
          nodesBlock8[(i-128)]?

def fastViews : QFast.Table View := ⟨63,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨132,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,47,46,45,44,43,42,41,40,0,0,0,0,0,0,0,0,39,38,37,36,35,34,33,32,63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0,55,54,53,52,51,50,49,48,0,0,0,0,0,0,0,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,15,14,13,12,23,22,21,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,15,14,11,10,23,22,19,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,15,13,11,9,23,21,19,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,24,25,26,27,32,33,34,35,48,49,50,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,15,14,13,12,11,10,9,8,31,30,29,28,27,26,25,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,16,0,17,0,18,0,19,0,24,0,25,0,26,0,27,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,48,0,49,0,50,0,51,0,56,0,57,0,58,0,59,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,47,45,43,41,39,37,35,33,63,61,59,57,55,53,51,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[63,61,59,57,31,29,27,25,55,53,51,49,23,21,19,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[63,61,47,45,31,29,15,13,55,53,39,37,23,21,7,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,63,0,61,0,55,0,53,0,43,0,41,0,35,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,29,0,23,0,21,0,11,0,9,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,37,39,41,43,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[63,59,47,43,31,27,15,11,55,51,39,35,23,19,7,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,63,0,59,0,55,0,51,0,45,0,41,0,37,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,27,0,23,0,19,0,13,0,9,0,5,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,63,0,55,0,47,0,39,0,57,0,49,0,41,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,23,0,15,0,7,0,25,0,17,0,9,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,1,0,5,0,17,0,21,0,9,0,13,0,25,0,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,37,0,49,0,53,0,41,0,45,0,57,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,1,0,3,0,17,0,19,0,9,0,11,0,25,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,35,0,49,0,51,0,41,0,43,0,57,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,37,39,49,51,53,55,1,3,5,7,17,19,21,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,0,0,0,0,0,0,1,3,9,11,21,23,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,1,5,9,13,19,23,27,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,0,0,0,0,0,0,0,1,7,9,15,17,23,25,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,0,0,0,0,0,0,0,3,7,9,13,19,23,25,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,0,0,0,0,0,0,0,5,7,9,11,21,23,25,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap26 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap27 : Array Nat := #[0,0,1,0,2,0,3,0,8,0,9,0,10,0,11,0,16,0,17,0,18,0,19,0,24,0,25,0,26,0,27,0,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap28 : Array Nat := #[0,0,0,0,0,0,0,0,30,28,26,24,14,12,10,8,63,61,59,57,47,45,43,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,0,0,0,0,0,0,33,37,41,45,49,53,57,61,0,4,8,12,16,20,24,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,41,43,49,51,57,59,0,2,8,10,16,18,24,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,37,39,41,43,45,47,0,2,4,6,8,10,12,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap33 : Array Nat := #[0,0,1,0,4,0,5,0,8,0,9,0,12,0,13,0,16,0,17,0,20,0,21,0,24,0,25,0,28,0,29,0,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap34 : Array Nat := #[0,2,4,6,16,18,20,22,8,10,12,14,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,34,36,38,48,50,52,54,40,42,44,46,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap35 : Array Nat := #[0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap36 : Array Nat := #[0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,36,37,48,49,52,53,40,41,44,45,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,48,49,50,51,40,41,42,43,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[0,0,0,0,0,0,0,0,36,37,38,39,52,53,54,55,4,5,6,7,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap40 : Array Nat := #[0,0,0,0,0,0,0,0,34,35,38,39,50,51,54,55,2,3,6,7,18,19,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,0,0,0,0,0,0,0,34,35,38,39,42,43,46,47,0,1,4,5,8,9,12,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap43 : Array Nat := #[0,31,0,30,0,29,0,28,0,23,0,22,0,21,0,20,0,27,0,26,0,25,0,24,0,19,0,18,0,17,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap44 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap45 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap46 : Array Nat := #[0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,1,3,5,7,8,10,12,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[0,2,4,6,16,18,20,22,8,10,12,14,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap48 : Array Nat := #[0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,2,3,6,7,8,9,12,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap49 : Array Nat := #[0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap50 : Array Nat := #[0,0,0,0,0,0,0,0,20,21,22,23,24,25,26,27,4,5,6,7,8,9,10,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap51 : Array Nat := #[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap5)
  | 2 => some (0, aliasMap4)
  | 3 => some (0, aliasMap3)
  | 4 => some (0, aliasMap25)
  | 5 => some (0, aliasMap24)
  | 6 => some (0, aliasMap23)
  | 7 => some (0, aliasMap22)
  | 8 => some (0, aliasMap21)
  | 9 => some (0, aliasMap14)
  | 14 => some (10, aliasMap51)
  | 15 => some (11, aliasMap50)
  | 16 => some (10, aliasMap49)
  | 17 => some (11, aliasMap48)
  | 18 => some (10, aliasMap47)
  | 19 => some (11, aliasMap46)
  | 20 => some (12, aliasMap45)
  | 21 => some (12, aliasMap44)
  | 22 => some (11, aliasMap8)
  | 23 => some (12, aliasMap43)
  | 24 => some (11, aliasMap7)
  | 25 => some (11, aliasMap31)
  | 26 => some (11, aliasMap42)
  | 27 => some (11, aliasMap35)
  | 28 => some (11, aliasMap6)
  | 29 => some (11, aliasMap2)
  | 30 => some (11, aliasMap20)
  | 31 => some (11, aliasMap40)
  | 32 => some (11, aliasMap39)
  | 33 => some (11, aliasMap38)
  | 34 => some (11, aliasMap41)
  | 35 => some (11, aliasMap30)
  | 36 => some (13, aliasMap19)
  | 37 => some (11, aliasMap29)
  | 38 => some (13, aliasMap18)
  | 39 => some (13, aliasMap17)
  | 40 => some (13, aliasMap16)
  | 41 => some (10, aliasMap15)
  | 42 => some (13, aliasMap13)
  | 43 => some (10, aliasMap12)
  | 44 => some (11, aliasMap28)
  | 45 => some (10, aliasMap11)
  | 46 => some (11, aliasMap10)
  | 53 => some (48, aliasMap37)
  | 54 => some (48, aliasMap36)
  | 55 => some (48, aliasMap34)
  | 56 => some (51, aliasMap33)
  | 57 => some (52, aliasMap32)
  | 58 => some (51, aliasMap27)
  | 59 => some (52, aliasMap26)
  | 60 => some (52, aliasMap9)
  | 61 => some (50, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 15 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 31 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 15 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 63 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 31 joinRoots_0_0 joinRoots_0_32

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 63 = true := joinRoots_1_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 12 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 blockNodes_72 blockNodes_84

theorem joinNodes_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 12 12 blockNodes_96 blockNodes_108

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 36 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 12 joinNodes_0_96 blockNodes_120

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 132 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 36 joinNodes_2_0 joinNodes_1_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 132 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfee8e880fe80e800 : Word) && vk v == 11 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfee8e880fe80e800 : BitVec 64) 11 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 62) = true := by decide +kernel
  cases ev : QFast.get fastViews 62 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12128_aux

open PEqualNP.Outside.L_meta_12128_aux in
theorem PEqualNP.Outside.L_meta_12128 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
