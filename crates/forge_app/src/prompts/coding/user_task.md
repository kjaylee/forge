<task>{{task}}</task>

{{#each files}}
<file_content path="{{this.path}}">
{{this.content}}
</file_content>

{{/each}}

{{#each focused_files}}
<focused_file>
{{this}}
</focused_file>

{{/each}}

{{#each opened_files}}
<opened_files>
{{this}}
</opened_files>

{{/each}}
