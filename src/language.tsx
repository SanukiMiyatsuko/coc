import Editor, { type Monaco } from '@monaco-editor/react';
import * as monaco from 'monaco-editor';

const languageDefinition: monaco.languages.IMonarchLanguage = {
  declarationKeywords: [
    'def', 'var'
  ],

  expressionKeywords: [
    'fun', 'forall', 'exist', 'let', 'in'
  ],

  typeKeywords: [
    'Prop', 'Type'
  ],

  operators: [
    '=>', '->', ':='
  ],

  symbols: /[=><!~?:&|+\-*/^%]+/,

  tokenizer: {
    root: [
      [/[A-Z][\w']*/, {
        cases: {
          '@typeKeywords': 'keyword.type',
          '@default': 'type.identifier',
        }
      }],
      
      [/[a-z_][\w']*/, {
        cases: {
          '@declarationKeywords': 'keyword.declaration',
          '@expressionKeywords': 'keyword.control',
          '@default': 'identifier'
        }
      }],

      { include: '@whitespace' },

      [/[()<>]/, '@brackets'],
      [/[;,]/, 'delimiter'],
      [/:(?!=)/, 'delimiter'],
      [/\.[01]/, 'operator'],

      [/@symbols/, {
        cases: {
          '@operators': 'operator',
          '@default': ''
        }
      }],
    ],

    whitespace: [
      [/\s+/, 'white'],
      [/--.*$/, 'comment'],
      [/\{-/, 'comment', '@comment'],
    ],

    comment: [
      [/[^{-]+/, 'comment'],
      [/\{-/, 'comment', '@push'],
      [/-}/, 'comment', '@pop'],
      [/[{-]/, 'comment']
    ],
  },
};

const customTheme: monaco.editor.IStandaloneThemeData = {
  base: 'vs-dark',
  inherit: true,
  rules: [
    { token: 'keyword.type', foreground: '4EC9B0', fontStyle: 'bold' },
    { token: 'type.identifier', foreground: '8FBC8F', fontStyle: 'bold' },
    { token: 'keyword.declaration', foreground: 'C586C0', fontStyle: 'bold' },
    { token: 'keyword.control', foreground: '00BFFF' },
    { token: 'identifier', foreground: '9CDCFE' },
    { token: 'operator', foreground: 'D4D4D4' },
    { token: 'comment', foreground: '6A9955', fontStyle: 'italic' },
  ],
  colors: {
    'editor.background': '#1e1e1e',
  }
};

export const CustomLanguageEditor = ({ source, replace }: { source: string;  replace: (_: string) => void }) => {
  function handleEditorWillMount(monaco: Monaco) {
    monaco.languages.register({ id: 'myLang' });
    monaco.languages.setMonarchTokensProvider('myLang', languageDefinition);
    monaco.editor.defineTheme('myTheme', customTheme);
  }
  return (
    <>
      <div style={{ 
        height: '800px', 
        border: '1px solid #333' 
      }}>
        <Editor
          height="100%"
          defaultLanguage="myLang"
          value={source}
          theme="myTheme"
          beforeMount={handleEditorWillMount}
          onChange={e => replace(e!)}
          options={{
            fontSize: 14,
            minimap: { enabled: true },
            automaticLayout: true,
            scrollBeyondLastLine: false,
            wordWrap: 'on',
          }}
        />
      </div>
    </>
  );
}