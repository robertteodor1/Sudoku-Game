import tkinter as tk
import random
import clips

class SudokuGui:
    def __init__(self, master):
        self.master = master
        master.title('Puzzle Sudoku')

        self.master.configure(bg='white')  # fundal general

        self.cells = {}
        self.selected_cell = None

        frame_board = tk.Frame(master, bg='black')
        frame_board.grid(row=0, column=0, padx=10, pady=10)


        frame_numbers = tk.Frame(master, bg='white')
        frame_numbers.grid(row=0, column=1, padx=10, pady=10)

        grid = [[0 for _ in range(9)] for _ in range(9)]
        self.generate_valid_sudoku(grid, clues=70)

        for row in range(9):
            for col in range(9):
                initial_value = grid[row][col]
                color = 'white' if initial_value != 0 else '#D0E9FF'

                entry = tk.Entry(frame_board, width=2, font=('Segoe UI', 20), justify='center',
                                 bd=0, bg=color, highlightthickness=1)

                # Linie groasă la fiecare 3 celule (pătratele mari 3x3)
                top_border = 3 if row % 3 == 0 else 1
                left_border = 3 if col % 3 == 0 else 1
                bottom_border = 3 if row == 8 else 1
                right_border = 3 if col == 8 else 1

                entry.grid(row=row, column=col, padx=(left_border, right_border), pady=(top_border, bottom_border))
                entry.config(highlightbackground='black', highlightcolor='black')

                if initial_value != 0:
                    entry.insert(0, str(initial_value))
                    entry.config(state='disabled', disabledforeground='black')

                entry.bind("<Button-1>", lambda e, r=row, c=col: self.select_cell(r, c))
                self.cells[(row, col)] = entry

        for i in range(9):
            for j in range(9):
                if grid[i][j] != 0:
                    self.cells[(i, j)].insert(0, str(grid[i][j]))
                    self.cells[(i, j)].config(state='disabled', disabledforeground='black')

        self.export_custom_facts()

        frame_numbers = tk.Frame(master)
        frame_numbers.grid(row=0, column=1, padx=10, pady=10)

        for num in range(1, 10):
            btn = tk.Button(frame_numbers, text=str(num), font=('Segoe UI', 18), width=3,
                            command=lambda n=num: self.add_completeaza_fact(n))
            btn.grid(row=(num-1)//3, column=(num-1)%3, padx=3, pady=3)

    def select_cell(self, row, col):
        self.selected_cell = (row, col)
        print(f"[INFO] Celulă selectată: ({row+1}, {col+1})")

    def add_completeaza_fact(self, numar):
        if self.selected_cell is None:
            print("[!] Selectează mai întâi o celulă.")
            return
        i, j = self.selected_cell
        entry = self.cells[(i, j)]
        if entry['state'] == 'disabled':
            print("[!] Nu poți modifica o celulă deja completată.")
            return
        entry.delete(0, tk.END)
        entry.insert(0, str(numar))
        self.append_completeaza_fact(i+1, j+1, numar)
        self.run_clips_rules()

    def append_completeaza_fact(self, i, j, n, filename='sudoku_fapte.clp'):
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()

        last_paren = content.rfind(")")
        if last_paren == -1:
            print("[!] Formatul fișierului nu este valid.")
            return

        new_fact = f"(completeaza {i} {j} {n})\n"
        new_content = content[:last_paren] + new_fact + content[last_paren:]

        with open(filename, 'w', encoding='utf-8') as f:
            f.write(new_content)

        print(f"[✓] Fapt inserat în deffacts: (completeaza {i} {j} {n})")

    def run_clips_rules(self):
        print("[INFO] Se rulează fișierul rules.clp cu CLIPS")
        env = clips.Environment()
        env.clear()
        env.load("rules.clp")
        env.load("sudoku_fapte.clp")
        env.reset()
        env.run()


    def export_custom_facts(self, filename='sudoku_fapte.clp'):
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("(deffacts Tabla\n")

            liniile = {i: [0]*9 for i in range(1, 10)}
            coloanele = {j: [0]*9 for j in range(1, 10)}

            for (row, col), entry in self.cells.items():
                i, j = row + 1, col + 1
                val = entry.get()
                n = int(val) if val != '' and entry['state'] == 'disabled' else 0

                f.write(f"(celula {i} {j} {n})\n")
                liniile[i][j - 1] = n
                coloanele[j][i - 1] = n

                if n != 0:
                    f.write(f"(este-pe-rand {i} cifra {n} {i} {j})\n")
                    f.write(f"(este-pe-coloana {j} cifra {n} {i} {j})\n")
                    square = 3 * ((i - 1) // 3) + ((j - 1) // 3) + 1
                    f.write(f"(este-in-patrat {square} cifra {n} {i} {j})\n")

            for i in range(1, 10):
                valori = ' '.join(str(x) for x in liniile[i])
                f.write(f"(linie {i} {valori})\n")
            for j in range(1, 10):
                valori = ' '.join(str(x) for x in coloanele[j])
                f.write(f"(coloana {j} {valori})\n")

            f.write(")\n")
        print(f"[✓] Deffacts complet salvat în {filename}")

    def fill_grid(self, grid):
        nums = list(range(1, 10))
        for i in range(9):
            for j in range(9):
                if grid[i][j] == 0:
                    random.shuffle(nums)
                    for n in nums:
                        if self.is_valid_grid(grid, i, j, n):
                            grid[i][j] = n
                            if self.fill_grid(grid):
                                return True
                            grid[i][j] = 0
                    return False
        return True

    def is_valid_grid(self, grid, i, j, n):
        if n in grid[i]:
            return False
        if n in [grid[r][j] for r in range(9)]:
            return False
        start_row, start_col = 3 * (i // 3), 3 * (j // 3)
        for r in range(start_row, start_row + 3):
            for c in range(start_col, start_col + 3):
                if grid[r][c] == n:
                    return False
        return True

    def generate_valid_sudoku(self, puzzle, clues=10):
        grid = [[0 for _ in range(9)] for _ in range(9)]
        self.fill_grid(grid)
        puzzle[:] = [row[:] for row in grid]
        cells_to_remove = 81 - clues
        while cells_to_remove > 0:
            i, j = random.randint(0, 8), random.randint(0, 8)
            if puzzle[i][j] != 0:
                puzzle[i][j] = 0
                cells_to_remove -= 1
        print(f"[INFO] Grilă Sudoku generată cu {clues} cifre și {81 - clues} celule goale")

# ===== Lansare aplicație =====
if __name__ == '__main__':
    root = tk.Tk()
    sudoku_gui = SudokuGui(root)
    root.mainloop()