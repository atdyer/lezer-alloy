import { parser } from '../dist/index.es';
import { flatIndent, continuedIndent, indentNodeProp, foldNodeProp, LezerSyntax } from '@codemirror/next/syntax';
import { Extension } from '@codemirror/next/state';

/**
 * A syntax provider based on the Lezer Alloy parser, extended
 * with highlighting and indentation information.
 */
export const alloySyntax = LezerSyntax.define(parser.withProps(
    indentNodeProp.add(type => {
        if (type.name == "BlockComment") return () => -1;
        return undefined;
    })
));

/**
 * Returns an extension that installs the Alloy syntax
 * and support features.
 */
export function alloy(): Extension {
    return [alloySyntax];
}