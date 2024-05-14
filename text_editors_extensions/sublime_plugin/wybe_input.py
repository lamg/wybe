import sublime
import sublime_plugin

class ReplaceListener(sublime_plugin.EventListener):
    def on_modified(self, view):
        cursor_pos = view.sel()[0].begin()

        last_two_chars = view.substr(sublime.Region(cursor_pos - 2, cursor_pos))
        
        sequences = {
            '==': '≡',
            '/=': '≢',
            '&&': '∧',
            '||': '∨',
            '=>': '⇒',
            '<=': '⇐',
            '-,': '¬',
            '|]': '□',
            '->': '→',
        }

        if last_two_chars in sequences:
            view.run_command('undo')
            view.run_command('insert', {'characters': sequences[last_two_chars]})